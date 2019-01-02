module FzipSpec where

import Test.Hspec

import Data.Bifunctor

import Fzip

var :: Int -> Term
var = Var . Variable

tvar :: Int -> Type
tvar = TVar . Variable

emp :: Context
emp = Context mempty

tc :: [Binding] -> Term -> Either Problem (Type, Context)
tc bs = first fromProblem . typecheck (Context bs)

spec :: Spec
spec = do
  describe "typecheck" $
    it "typechecks a term" $ do
      tc [] (var 0) `shouldBe` Left (UnboundVariable $ Variable 0)
      tc [] (var 1) `shouldBe` Left (UnboundVariable $ Variable 1)

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


      tc [] (Abs IntType $ var 0)  `shouldBe` return (IntType :-> IntType, emp)
      tc [] (Abs IntType $ var 1)  `shouldBe` Left (UnboundVariable $ Variable 1)
      tc [] (Abs (tvar 0) $ var 0) `shouldBe` Left (UnboundVariable $ Variable 0)
      tc [] (Abs (tvar 8) $ var 0) `shouldBe` Left (UnboundVariable $ Variable 8)

      tc [Universal] (Abs (tvar 0) $ var 0)    `shouldBe` return (tvar 0 :-> tvar 0, Context [Universal])
      tc [Term IntType] (Abs (tvar 0) $ var 0) `shouldBe` Left (NotTypeBinding $ Term IntType)
      tc [Existential] (Abs (tvar 0) $ var 0)  `shouldBe` Left (IllFormedOnPureContext (tvar 0) $ Context [Existential])

      tc [] (Abs (Forall $ tvar 0) $ var 0)          `shouldBe` return (Forall (tvar 0) :-> Forall (tvar 0), Context [])
      tc [Universal] (Abs (Forall $ tvar 0) $ var 0) `shouldBe` return (Forall (tvar 0) :-> Forall (tvar 0), Context [Universal])

      tc [] (Abs IntType $ Abs IntType $ var 0) `shouldBe` return (IntType :-> IntType :-> IntType, Context [])


      tc [] (Abs IntType (var 0) `App` var 0)                             `shouldBe` Left (UnboundVariable $ Variable 0)
      tc [] (Abs (IntType :-> IntType) (var 0) `App` Abs IntType (var 0)) `shouldBe` return (IntType :-> IntType, emp)
      tc [] (Abs IntType (var 0) `App` Abs IntType (var 0))               `shouldBe` Left (TypeMismatch IntType $ IntType :-> IntType)

      tc [Universal] (Abs (tvar 0) (var 0) `App` var 0) `shouldBe` Left (NotTermBinding Universal)

      let bs = [Term $ tvar 1, Universal] in
        tc bs (Abs (tvar 1) (var 0) `App` var 0) `shouldBe` return (tvar 1, Context bs)

      let bs = [Term $ tvar 1, Existential] in
        tc bs (Abs (tvar 1) (var 0) `App` var 0) `shouldBe` Left (IllFormedOnPureContext (tvar 1) $ Context bs)


      tc [] (Let (var 0) $ var 0)               `shouldBe` Left (UnboundVariable $ Variable 0)
      tc [] (Let (Abs IntType $ var 0) $ var 0) `shouldBe` return (IntType :-> IntType, emp)

      tc [Existential] (Let (Abs IntType $ var 0) $ var 0) `shouldBe` return (IntType :-> IntType, Context [Existential])

      tc [Existential, Term $ Some IntType] (Let (Open (Variable 0) $ var 1) $ var 0)                 `shouldBe` return (IntType, Context [Consumed, Term $ Some IntType])
      tc [Existential, Term $ Some $ tvar 0] (Let (Open (Variable 0) $ var 1) $ var 0)                `shouldBe` return (tvar 0, Context [Consumed, Term $ Some $ tvar 0])
      tc [Term $ tvar 1, Existential, Term $ Some $ tvar 0] (Let (Open (Variable 1) $ var 2) $ var 1) `shouldBe` return (tvar 1, Context [Term $ tvar 1, Consumed, Term $ Some $ tvar 0])
      tc [Term $ tvar 1, Existential, Term $ Some $ tvar 0] (Let (var 2) $ var 1)                     `shouldBe` Left (IllFormedOnPureContext (tvar 2) $ Context [Term $ Some $ tvar 0, Term $ tvar 2, Existential, Term $ Some $ tvar 0])


      tc [] (Open (Variable 0) $ var 1)                          `shouldBe` Left (UnboundVariable $ Variable 0)
      tc [Universal] (Open (Variable 0) $ var 1)                 `shouldBe` Left (NotExistentialBinding Universal)
      tc [Existential] (Open (Variable 0) $ var 1)               `shouldBe` Left (UnboundVariable $ Variable 0)
      tc [Existential, Term IntType] (Open (Variable 0) $ var 1) `shouldBe` Left (NotExistential IntType)

      tc [Existential, Term $ Some IntType] (Open (Variable 0) $ var 1)  `shouldBe` return (IntType, Context [Consumed, Term $ Some IntType])
      tc [Existential, Term $ Some $ tvar 0] (Open (Variable 0) $ var 1) `shouldBe` return (tvar 0, Context [Consumed, Term $ Some $ tvar 0])

      tc [Term $ tvar 1, Existential, Term $ Some IntType] (Open (Variable 1) $ var 2) `shouldBe` return (IntType, Context [Term $ tvar 1, Consumed, Term $ Some IntType])
      tc [Term $ tvar 1, Existential, Term $ Some $ tvar 0] (Open (Variable 1) $ var 2) `shouldBe` return (tvar 1, Context [Term $ tvar 1, Consumed, Term $ Some $ tvar 0])
