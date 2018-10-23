module TypeClassSpec where

import Test.Hspec

import qualified Data.Set as Set

import TypeClass

spec :: Spec
spec = do
  describe "reconstruct" $
    it "reconstructs a type" $ do
      reconstruct (Assump []) (Var 0)           `shouldBe` Left (UnboundVariable 0)
      reconstruct (Assump [scheme Int]) (Var 0) `shouldBe` return (Int, mempty)

      let i = Ident (-1)
          ty0 = TVar $ Ident 0
          clA = Class "A" in do
        reconstruct (Assump [Scheme (Set.singleton i) $ Qual mempty $ TVar i]) (Var 0)                          `shouldBe` return (TVar $ Ident 0, mempty)
        reconstruct (Assump [Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ TVar i]) (Var 0) `shouldBe` return (ty0, Set.singleton $ ty0 :< clA)

        reconstruct (Assump []) (Abs $ Var 0)               `shouldBe` return (ty0 :-> ty0, mempty)
        reconstruct (Assump []) (Abs $ App (Var 0) $ Var 0) `shouldBe` Left (Recursive (Ident 0) $ ty0 :-> TVar (Ident 1))
