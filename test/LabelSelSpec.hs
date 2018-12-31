{-# OPTIONS_GHC -Wno-orphans #-}

module LabelSelSpec where

import Test.Hspec
import Test.QuickCheck

import qualified Data.Map.Lazy as Map

import LabelSel

instance Arbitrary Symbol where
  arbitrary = Symbol <$> arbitrary

instance Arbitrary Label where
  arbitrary = Label <$> arbitrary <*> arbitrary `suchThat` (1 <=)

instance Arbitrary Base where
  arbitrary = oneof
    [ return Int
    , return Bool
    ]

instance Arbitrary Type where
  arbitrary = sized arbType

arbType :: Int -> Gen Type
arbType n = oneof
  [ Base <$> arbitrary
  , (:->) <$> arbRecord n <*> arbitrary
  ]

instance Arbitrary Record where
  arbitrary = sized arbRecord

arbRecord :: Int -> Gen Record
arbRecord m = Record <$> f m
  where f 0 = return Map.empty
        f n = Map.insert <$> arbitrary <*> arbType (n `div` 2) <*> sub
          where sub = f $ n `div` 2

spec :: Spec
spec = do
  let sym = Symbol "s0"
  let l = Label sym 1
  let ty = Base Int

  let sym1 = Symbol "s1"
  let l1 = Label sym1 1

  describe "free" $
    it "adjusts a record by another record" $ do
      free mempty sym 1 `shouldBe` 1

  describe "adjust" $
    it "adjusts a record by another record" $ do
      adjust mempty (Record $ Map.singleton l ty) `shouldBe` Record (Map.singleton l ty)

  describe "concatR" $ do
    it "concatenates two records" $ do
      mempty `concatR` mempty                                                       `shouldBe` mempty
      mempty `concatR` (Record $ Map.singleton l ty)                                `shouldBe` Record (Map.singleton l ty)
      Record (Map.singleton l $ Base Bool) `concatR` (Record $ Map.singleton l ty)  `shouldBe` Record (Map.fromList [(l, Base Bool), (Label sym 2, ty)])
      Record (Map.singleton l1 $ Base Bool) `concatR` (Record $ Map.singleton l ty) `shouldBe` Record (Map.fromList [(l1, Base Bool), (l, ty)])

    it "the empty record is the right unit" $ property $
      \r -> r `concatR` mempty `shouldBe` r

    it "the empty record is the left unit" $ property $
      \r -> mempty `concatR` r `shouldBe` r

    it "is associative" $ property $
      \(r, s, t) -> r `concatR` s `concatR` t `shouldBe` (concatR r $ concatR s t)
