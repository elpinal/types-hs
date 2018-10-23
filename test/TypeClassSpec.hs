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
          ty2 = TVar $ Ident 2
          clA = Class "A" in do
        reconstruct (Assump [Scheme (Set.singleton i) $ Qual mempty $ TVar i]) (Var 0)                          `shouldBe` return (TVar $ Ident 0, mempty)
        reconstruct (Assump [Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ TVar i]) (Var 0) `shouldBe` return (ty0, Set.singleton $ ty0 :< clA)

        reconstruct (Assump []) (Abs $ Var 0)                     `shouldBe` return (ty0 :-> ty0, mempty)
        reconstruct (Assump []) (Abs $ App (Var 0) $ Var 0)       `shouldBe` Left (Recursive (Ident 0) $ ty0 :-> TVar (Ident 1))
        reconstruct (Assump []) (Abs $ Abs $ App (Var 0) $ Var 1) `shouldBe` return (ty0 :-> (ty0 :-> ty2) :-> ty2, mempty)

        reconstruct (Assump [Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ TVar i :-> Int]) (Var 0) `shouldBe` return (ty0 :-> Int, Set.singleton $ ty0 :< clA)
        reconstruct (
          Assump
            [ Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ TVar i :-> Int
            , scheme Int
            ]
          ) (Var 0 `App` Var 1) `shouldBe` return (Int, Set.singleton $ Int :< clA)
        reconstruct (
          Assump
            [ Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ TVar i :-> Int
            , Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ Int :-> TVar i
            , scheme Int
            ]
          ) (Var 0 `App` (Var 1 `App` Var 2)) `shouldBe` return (Int, Set.singleton $ ty2 :< clA)
        reconstruct (
          Assump
            [ Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ TVar i :-> Int
            , Scheme (Set.singleton i) $ Qual (Set.singleton $ TVar i :< clA) $ Int :-> TVar i
            , scheme Int
            ]
          ) (Let (Var 0 `App` (Var 1 `App` Var 2)) $ Var 0) `shouldBe` Left (Ambiguous $ Scheme (Set.singleton $ Ident 2) $ Qual (Set.singleton $ ty2 :< clA) Int)
