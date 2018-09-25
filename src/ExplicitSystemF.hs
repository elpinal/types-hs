{-# LANGUAGE DeriveFunctor #-}

module ExplicitSystemF
  ( Expr(..)
  , Term(..)
  , var
  , forall
  , arr
  , Explicit(..)
  , explicit
  , Subst(..)
  , ETerm(..)
  , foldExpr
  , nf
  , reduce
  , equal
  , substTop
  ) where

import Control.Monad.Trans.State

data Expr f = In (f (Expr f))

data Term a
  = Var Int
  | Forall a
  | Arr a a
  deriving Functor

term :: Term (Expr ETerm) -> Expr ETerm
term = In . Inl

var :: Int -> Expr ETerm
var = term . Var

forall :: Expr ETerm -> Expr ETerm
forall = term . Forall

arr :: Expr ETerm -> Expr ETerm -> Expr ETerm
arr x y = term $ Arr x y

data Explicit a = Explicit a (Subst a)
  deriving Functor

explicit :: Expr ETerm -> Subst (Expr ETerm) -> Expr ETerm
explicit e = In . Inr . Explicit e

data Subst a
  = Id
  | Shift
  | Cons a (Subst a)
  | Comp (Subst a) (Subst a)
  deriving Functor

data ETerm a
  = Inl (Term a)
  | Inr (Explicit a)
  deriving Functor

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In x) = f $ foldExpr f <$> x

class Render f where
  render :: Render g => f (Expr g) -> String

pretty :: Render f => Expr f -> String
pretty (In x) = render x

instance Render Term where
  render (Var n) = show n
  render (Forall t) = "(forall." ++ pretty t ++ ")"
  render (Arr t1 t2) = "(" ++ pretty t1 ++ " -> " ++ pretty t2 ++ ")"

instance Render Subst where
  render Id = "id"
  render Shift = "shift"
  render (Cons x y) = "(" ++ pretty x ++ " `cons` " ++ render y ++ ")"
  render (Comp x y) = "(" ++ render x ++ " `comp` " ++ render y ++ ")"

instance Render Explicit where
  render (Explicit x y) = "(" ++ pretty x ++ "[" ++ render y ++ "])"

instance Render ETerm where
  render (Inl t) = render t
  render (Inr e) = render e

class Whnf f where
  whnf :: f (Expr ETerm) -> State (Subst (Expr ETerm)) (Term (Expr ETerm))

instance Whnf Term where
  whnf (Var n) = do
    s <- get
    case s of
      Id -> return $ Var n
      Shift -> put Id >> return (Var $ n + 1)
      Cons t s' -> case n of
        0 -> case t of
          (In (Inr (Explicit (In t) s0))) -> put s0 >> whnf t
          _ -> error $ "unexpected error: " ++ pretty t
        _ -> put s' >> whnf (Var $ n - 1)
      Comp s1 s2 -> put s2 >> whnf (Inr $ Explicit (var n) s1)
  whnf t = return t

instance Whnf Explicit where
  whnf (Explicit (In (Inl (Var n))) s0) = case s0 of
    Id -> whnf $ Var n
    Shift -> whnf $ Var $ n + 1
    Cons (In t) s -> case n of
      0 -> whnf t
      _ -> whnf $ Explicit (var $ n - 1) s
    Comp s1 s2 -> withState (Comp s2) $ whnf $ Inr $ Explicit (var n) s1
  whnf (Explicit (In t) s) = withState (Comp s) $ whnf t

instance Whnf ETerm where
  whnf (Inl t) = whnf t
  whnf (Inr e) = whnf e

nf :: Whnf f => f (Expr ETerm) -> Subst (Expr ETerm) -> Expr Term
nf x s0 =
  let (y, s) = runState (whnf x) s0 in
    case y of
      Forall (In a) -> In $ Forall $ nf a $ beta s
      Arr (In a) (In b) -> In $ nf a s `Arr` nf b s
      Var n -> In $ Var n

reduce :: Expr ETerm -> Expr Term
reduce (In e) = nf e Id

beta :: Subst (Expr ETerm) -> Subst (Expr ETerm)
beta s = explicit (var 0) Id `Cons` Comp s Shift

equalS :: Expr ETerm -> Subst (Expr ETerm) -> Expr ETerm -> Subst (Expr ETerm) -> Bool
equalS (In x) u1 (In y) u2 =
  let (a, s1) = runState (whnf x) u1 in
  let (b, s2) = runState (whnf y) u2 in
  case (a, b) of
    (Var m, Var n) -> m == n
    (Arr t11 t12, Arr t21 t22) -> equalS t11 s1 t21 s2 && equalS t12 s1 t22 s2
    (Forall t1, Forall t2) -> equalS t1 (beta s1) t2 (beta s2)
    _ -> False

equal :: Expr ETerm -> Expr ETerm -> Bool
equal x y = equalS x Id y Id

substTop :: Expr ETerm -> Expr ETerm -> Expr ETerm
substTop x y = explicit x $ Cons y Id
