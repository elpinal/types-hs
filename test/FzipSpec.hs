module FzipSpec where

import Test.Hspec

import Fzip

var :: Int -> Term
var = Var . Variable

tvar :: Int -> Type
tvar = TVar . Variable

emp :: Context
emp = Context mempty

tc :: [Binding] -> Term -> Either TypeError (Type, Context)
tc = typecheck . Context

spec :: Spec
spec = do
  describe "typecheck" $
    it "typechecks a term" $ do
      typecheck emp (var 0) `shouldBe` Left (UnboundVariable $ Variable 0)
      typecheck emp (var 1) `shouldBe` Left (UnboundVariable $ Variable 1)

      tc [Term IntType] (var 0) `shouldBe` return (IntType, Context [Term IntType])
      tc [Term IntType] (var 1) `shouldBe` Left (UnboundVariable $ Variable 1)

      let bs = [Term $ tvar 1, Universal] in
        tc bs (var 0) `shouldBe` return (tvar 1, Context bs)

      let bs = [Term $ tvar 1, Existential] in
        tc bs (var 0) `shouldBe` Left (IllFormedOnPureContext (tvar 1) $ Context bs)

      let bs = [Term $ tvar 1, Def $ tvar 2, Universal] in
        tc bs (var 0) `shouldBe` return (tvar 1, Context bs)

      let bs = [Term $ tvar 1, Def $ tvar 2, Existential] in
        tc bs (var 0) `shouldBe` Left (IllFormedOnPureContext (tvar 2) $ Context bs)


      typecheck emp (Abs IntType $ var 0)  `shouldBe` return (IntType :-> IntType, emp)
      typecheck emp (Abs IntType $ var 1)  `shouldBe` Left (UnboundVariable $ Variable 1)
      typecheck emp (Abs (tvar 0) $ var 0) `shouldBe` Left (UnboundVariable $ Variable 0)
      typecheck emp (Abs (tvar 8) $ var 0) `shouldBe` Left (UnboundVariable $ Variable 8)

      tc [Universal] (Abs (tvar 0) $ var 0)    `shouldBe` return (tvar 0 :-> tvar 0, Context [Universal])
      tc [Term IntType] (Abs (tvar 0) $ var 0) `shouldBe` Left (NotTypeBinding $ Term IntType)
      tc [Existential] (Abs (tvar 0) $ var 0)  `shouldBe` Left (IllFormedOnPureContext (tvar 0) $ Context [Existential])

      typecheck emp (Abs (Forall $ tvar 0) $ var 0)  `shouldBe` return (Forall (tvar 0) :-> Forall (tvar 0), Context [])
      tc [Universal] (Abs (Forall $ tvar 0) $ var 0) `shouldBe` return (Forall (tvar 0) :-> Forall (tvar 0), Context [Universal])

      typecheck emp (Abs IntType $ Abs IntType $ var 0) `shouldBe` return (IntType :-> IntType :-> IntType, Context [])
