{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}

module Main where

import Data.Constraint (Dict (..))
import Data.Functor.Identity (runIdentity)
import Data.Singletons
import Data.Singletons.TH
import Data.Typeable (Typeable)
import Data.TypeRepMap (TypeRepMap)

import Data.Singletons.Dict

import Test.Tasty
import Test.Tasty.Hspec

import qualified Data.TypeRepMap as TRM


$(singletons [d|
    data Field
        = BoolField
        | IntField
        | StringField
        deriving (Bounded, Enum, Eq, Ord, Show)
    |])

$(mkTotalDictGetter ''SField ''Typeable)


data FieldValue (field :: Field) where
    BoolValue   :: Bool   -> FieldValue 'BoolField
    IntValue    :: Int    -> FieldValue 'IntField
    StringValue :: String -> FieldValue 'StringField


class Validated (field :: Field) where
    isValid :: FieldValue field -> Bool
    isValid _ = True

instance Validated BoolField   where
instance Validated IntField    where
instance Validated StringField where

$(mkTotalDictGetter ''SField ''Validated)


class HasIntValue (field :: Field) where
    intValue :: FieldValue field -> Int

instance HasIntValue IntField where
    intValue (IntValue n) = n

$(mkPartialDictGetter ''SField ''HasIntValue)


fieldTypes :: [Field]
fieldTypes = enumFrom BoolField

mkFieldMap :: [Field] -> TypeRepMap FieldValue
mkFieldMap = foldr TRM.union TRM.empty . fmap mkSingleFieldMap

mkSingleFieldMap :: Field -> TypeRepMap FieldValue
mkSingleFieldMap field = withSomeSing field $ \(singField :: SField field) ->
    runIdentity $ do
        Dict <- fieldTypeableDictA singField
        pure $ TRM.one @field $ testFieldValue singField

testFieldValue :: SField field -> FieldValue field
testFieldValue = \case
    SBoolField   -> BoolValue   True
    SIntField    -> IntValue    1
    SStringField -> StringValue "test"


main :: IO ()
main = do
    specs <- sequence
        [ testSpec "Total"   totalGetterSpec
        , testSpec "Partial" partialGetterSpec
        ]
    defaultMain $ testGroup "Tests" specs


totalGetterSpec :: Spec
totalGetterSpec = describe "mkTotalDictGetter" $ do
    it "generates a Dict getter for all the promoted data constructors" $ do
        fieldValidatedDict SBoolField    `shouldBe` Dict
        fieldValidatedDict SIntField     `shouldBe` Dict
        fieldValidatedDict SStringField  `shouldBe` Dict
        TRM.size (mkFieldMap fieldTypes) `shouldBe` length fieldTypes

partialGetterSpec :: Spec
partialGetterSpec = describe "mkPartialDictGetter" $ do
    it "generates a Dict getter for all the promoted data constructors that are instances of the class" $ do
        fieldHasIntValueDict SBoolField   `shouldBe` Nothing
        fieldHasIntValueDict SIntField    `shouldBe` Just Dict
        fieldHasIntValueDict SStringField `shouldBe` Nothing
