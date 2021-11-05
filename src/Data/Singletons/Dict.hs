{-# LANGUAGE CPP             #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module Data.Singletons.Dict
       (
         mkTotalDictGetter
       , mkPartialDictGetter
       ) where

import Data.Bifunctor (bimap, first, second)
import Data.Bool (bool)
import Data.Char (toLower)
import Data.Constraint (Dict (..))
import Data.Foldable (traverse_)
import Data.Typeable (Typeable)
import Language.Haskell.TH


-- | Generates 'Dict' getters for the promoted nullary data constructors corresponding to
-- a @singletons@-like type.
--
-- __All the promoted data constructors must be instances of the given type class.__
--
-- The names of the getters result from the concatenation of:
--
-- * the camel-cased name of the base type,
-- * the name of the type class,
-- * the "'Dict'" keyword,
-- * the \"A\" suffix, for the contextual getter.
--
-- /Example:/
--
-- Given this type:
--
-- @
-- data Example = Foo | Bar | Baz
-- @
--
-- and the corresponding @singletons@-like type:
--
-- @
-- data SExample (example :: Example) where
--     SFoo :: SExample 'Foo
--     SBar :: SExample 'Bar
--     SBaz :: SExample 'Baz
-- @
--
-- this line:
--
-- @
-- \$(mkTotalDictGetter ''SExample '''Typeable')
-- @
--
-- generates those getters:
--
-- @
-- exampleTypeableDict :: SExample example -> 'Dict' ('Typeable' example)
-- exampleTypeableDict sing =
--     case sing of
--         SFoo -> 'Dict'
--         SBar -> 'Dict'
--         SBaz -> 'Dict'
--
-- exampleTypeableDictA :: 'Applicative' f => SExample example -> f ('Dict' ('Typeable' example))
-- exampleTypeableDictA sing =
--     case sing of
--         SFoo -> 'pure' 'Dict'
--         SBar -> 'pure' 'Dict'
--         SBaz -> 'pure' 'Dict'
-- @
mkTotalDictGetter
    :: Name
    -- ^ The 'Name' of a @singletons@-like type.
    -> Name
    -- ^ The 'Name' of a type class.
    -> Q [Dec]
mkTotalDictGetter singTypeName className = reify singTypeName >>= \case
#if MIN_VERSION_template_haskell(2,17,0)
    TyConI (DataD [] _ [ KindedTV _ _ (ConT baseTypeName) ] Nothing cons []) -> do
#else
    TyConI (DataD [] _ [ KindedTV _   (ConT baseTypeName) ] Nothing cons []) -> do
#endif
        checkSingleParamClassName className
        (conSingNames, conTypes) <- unzip <$> traverse singConData cons
        traverse_ checkConTypeInstance conTypes

        let singType      = conT singTypeName
        let classType     = conT className
        let baseFunName   = mkGetterName baseTypeName className "Dict"
        let liftedFunName = mkGetterName baseTypeName className "DictA"

        sequence
            [ sigD
                baseFunName
                [t| forall a. $singType a -> Dict ($classType a) |]
            , mkGetterBody
                baseFunName
                (zip conSingNames $ repeat (normalB [e| Dict |]))
            , sigD
                liftedFunName
                 [t| forall a f. Applicative f => $singType a -> f (Dict ($classType a)) |]
            , mkGetterBody
                liftedFunName
                (zip conSingNames $ repeat (normalB [e| pure Dict |]))
            ]

    invalid -> fail $ invalidTypeError singTypeName invalid
  where
    checkConTypeInstance :: Type -> Q ()
    checkConTypeInstance conType
        = unlessM (isInstance' className conType)
        $ fail
        $ typeName <> " is not an instance of `" <> nameBase className <> "'."
      where
        typeName = case conType of
            ConT name      -> quotedName name
            PromotedT name -> quotedName name
            _              -> show conType

-- | Generates 'Dict' getters for the promoted nullary data constructors corresponding to
-- a @singletons@-like type.
--
-- __Not all the promoted data constructors must be instances of the given type class.__
--
-- The name of the getters results from the concatenation of:
--
-- * the camel-cased name of the base type,
-- * the name of the type class,
-- * the "'Dict'" keyword,
-- * the \"A\" suffix, for the contextual getter.
--
-- /Example:/
--
-- Given this type:
--
-- @
-- data Example = Foo | Bar | Baz
-- @
--
-- the corresponding @singletons@-like type:
--
-- @
-- data SExample (example :: Example) where
--     SFoo :: SExample 'Foo
--     SBar :: SExample 'Bar
--     SBaz :: SExample 'Baz
-- @
--
-- and this type class and instance:
--
-- @
-- class IsBar (a :: k) where
--
-- instance IsBar 'Bar where
-- @
--
-- this line:
--
-- @
-- \$(mkPartialDictGetter ''SExample ''IsBar)
-- @
--
-- generates those getters:
--
-- @
-- exampleIsBarDict :: SExample example -> 'Maybe' ('Dict' (IsBar example))
-- exampleIsBarDict sing =
--     case sing of
--         SFoo -> 'Nothing'
--         SBar -> 'Just' 'Dict'
--         SBaz -> 'Nothing'
--
-- exampleIsBarDictA :: 'Applicative' f => SExample example -> f ('Maybe' ('Dict' (IsBar example)))
-- exampleIsBarDictA sing =
--     case sing of
--         SFoo -> 'pure' 'Nothing'
--         SBar -> 'pure' ('Just' 'Dict')
--         SBaz -> 'pure' 'Nothing'
-- @
mkPartialDictGetter
    :: Name
    -- ^ The 'Name' of a @singletons@-like type.
    -> Name
    -- ^ The 'Name' of a type class.
    -> Q [Dec]
mkPartialDictGetter singTypeName className = reify singTypeName >>= \case
#if MIN_VERSION_template_haskell(2,17,0)
    TyConI (DataD [] _ [ KindedTV _ _ (ConT baseTypeName) ] Nothing cons []) -> do
#else
    TyConI (DataD [] _ [ KindedTV _   (ConT baseTypeName) ] Nothing cons []) -> do
#endif
        checkSingleParamClassName className
        cons' <- traverse singConData cons >>= partitionM (isInstance' className . snd)

        let singType      = conT singTypeName
        let classType     = conT className
        let baseFunName   = mkGetterName baseTypeName className "Dict"
        let liftedFunName = mkGetterName baseTypeName className "DictA"
        let (dictSingNames, voidSingNames) = bimap (fmap fst) (fmap fst) cons'

        sequence
            [ sigD
                baseFunName
                [t| forall a. $singType a -> Maybe (Dict ($classType a)) |]
            , mkGetterBody
                baseFunName
                ( zip voidSingNames (repeat (normalB [e| Nothing |])) <>
                  zip dictSingNames (repeat (normalB [e| Just Dict |]))
                )
            , sigD
                liftedFunName
                [t| forall a f. Applicative f => $singType a -> f (Maybe (Dict ($classType a))) |]
            , mkGetterBody
                liftedFunName
                ( zip voidSingNames (repeat (normalB [e| pure Nothing |])) <>
                  zip dictSingNames (repeat (normalB [e| pure (Just Dict) |]))
                )
            ]

    invalid -> fail $ invalidTypeError singTypeName invalid


mkGetterName :: Name -> Name -> String -> Name
mkGetterName (nameBase -> baseTypeName) (nameBase -> className) suffix
     = mkName
     $ toLower (head baseTypeName)
     : tail baseTypeName
    <> className
    <> suffix

mkGetterBody :: Name -> [(Name, BodyQ)] -> DecQ
mkGetterBody name matches
    = funD name
    [ clause
        [ varP paramName ]
        (normalB (caseE (varE paramName) (mkCaseMatch <$> matches)))
        []
    ]
  where
    paramName :: Name
    paramName = mkName "sing"

    mkCaseMatch :: (Name, BodyQ) -> MatchQ
    mkCaseMatch (singName, body) = match (conP singName []) body []


singConData :: Con -> Q (Name, Type)
singConData con = case con of
    GadtC [ singName ] [] (AppT _ baseType) -> pure (singName, baseType)
    _ -> fail $ expectationError "nullary GADT data constructor" (conLabel con)

checkSingleParamClassName :: Name -> Q ()
checkSingleParamClassName name = reify name >>= \case
    ClassI (ClassD _ _ [ _ ] _ _) _ -> pure ()
    invalid -> fail $ invalidClassError name invalid

isInstance' :: Name ->  Type -> Q Bool
isInstance' className
    | className == ''Typeable
    = const $ pure True
    | otherwise
    = isInstance className . pure

infoValueLabel :: Info -> String
infoValueLabel = \case
    ClassI _ _       -> "type class"
    ClassOpI _ _ _   -> "type class method"
    DataConI _ _ _   -> "data constructor"
    FamilyI _ _      -> "type or data family"
    PatSynI _ _      -> "pattern synonym"
    PrimTyConI _ _ _ -> "primitive type constructor"
    TyConI _         -> "type constructor"
    TyVarI _ _       -> "type variable"
    VarI _ _ _       -> "value variable"

conLabel :: Con -> String
conLabel con = shapeLabel <> " (" <> conName <> ")"
  where
    conName, shapeLabel :: String
    (quotedName -> conName, shapeLabel) = conData con

    conData :: Con -> (Name, String)
    conData = \case
        ForallC _ _ con'       -> conData con'
        GadtC (name : _) [] _  -> (name, "nullary GADT data constructor")
        GadtC (name : _) _ _   -> (name, "non-nullary GADT data constructor")
        InfixC _ name _        -> (name, "infix data constructor")
        NormalC name _         -> (name, "normal data constructor")
        RecC name _            -> (name, "recursive normal data constructor")
        RecGadtC (name :_) _ _ -> (name, "recursive GADT data constructor")

quotedName :: Name -> String
quotedName name = "`" <> nameBase name <> "'"


invalidTypeError :: Name -> Info -> String
invalidTypeError name invalid
    = expectationError
        "singletons-like type constructor"
        (invalidLabel <> " (" <> quotedName name <> ")")
  where
    invalidLabel :: String
    invalidLabel = case invalid of
        TyConI _ -> "non singletons-like type constructor"
        _        -> infoValueLabel invalid

invalidClassError :: Name -> Info -> String
invalidClassError name invalid
    = expectationError
        "single-parameter type class"
        (invalidLabel <> " (" <> quotedName name <> ")")
  where
    invalidLabel :: String
    invalidLabel = case invalid of
        ClassI _ _ -> "multi-parameter type class"
        _          -> infoValueLabel invalid

expectationError :: String -> String -> String
expectationError expected got = unlines
    [ ""
    , "Expected:"
    , ""
    , "    " <> expected <> ","
    , ""
    , "Got:"
    , ""
    , "    " <> got <> "."
    , ""
    ]


unlessM :: Monad m => m Bool -> m () -> m ()
unlessM test action = test >>= bool action (pure ())

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f = \case
    []       -> pure ([], [])
    (x : xs) -> do
        result <- f x
        bool second first result (x :) <$> partitionM f xs
