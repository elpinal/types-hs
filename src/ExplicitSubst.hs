module ExplicitSubst
  ( Expr(..)
  , Term(..)
  , var
  , lam
  , app
  , Explicit(..)
  , explicit
  , Subst(..)
  , ETerm(..)
  , foldExpr
  , nf
  , reduce
  ) where

import Control.Monad.Trans.State

data Expr f = In (f (Expr f))

data Term a
  = Var Int
  | Abs a
  | App a a

term :: Term (Expr ETerm) -> Expr ETerm
term = In . Inl

var :: Int -> Expr ETerm
var = term . Var

lam :: Expr ETerm -> Expr ETerm
lam = term . Abs

app :: Expr ETerm -> Expr ETerm -> Expr ETerm
app x y = term $ App x y

data Explicit a = Explicit a (Subst a)

explicit :: Expr ETerm -> Subst (Expr ETerm) -> Expr ETerm
explicit e = In . Inr . Explicit e

data Subst a
  = Id
  | Shift
  | Cons a (Subst a)
  | Comp (Subst a) (Subst a)

data ETerm a
  = Inl (Term a)
  | Inr (Explicit a)

instance Functor Term where
  fmap _ (Var n) = Var n
  fmap f (Abs x) = Abs $ f x
  fmap f (App x y) = App (f x) (f y)

instance Functor Explicit where
  fmap f (Explicit x y) = Explicit (f x) $ fmap f y

instance Functor Subst where
  fmap _ Id = Id
  fmap _ Shift = Shift
  fmap f (Cons x y) = Cons (f x) $ fmap f y
  fmap f (Comp x y) = Comp (fmap f x) $ fmap f y

instance Functor ETerm where
  fmap f (Inl t) = Inl $ fmap f t
  fmap f (Inr s) = Inr $ fmap f s

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In x) = f $ foldExpr f <$> x

class Render f where
  render :: Render g => f (Expr g) -> String

pretty :: Render f => Expr f -> String
pretty (In x) = render x

instance Render Term where
  render (Var n) = show n
  render (Abs t) = "(lamda." ++ pretty t ++ ")"
  render (App t1 t2) = "(" ++ pretty t1 ++ " " ++ pretty t2 ++ ")"

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
  whnf :: f (Expr ETerm) -> State (Subst (Expr ETerm)) (Expr ETerm)

instance Whnf Term where
  whnf (Var n) = do
    s <- get
    case s of
      Id -> return $ var n
      Shift -> put Id >> return (var $ n + 1)
      Cons t s' -> case n of
        0 -> case t of
          (In (Inr (Explicit (In t) s0))) -> put s0 >> whnf t
          _ -> error $ "unexpected error: " ++ pretty t
        _ -> put s' >> whnf (Var $ n - 1)
      Comp s1 s2 -> put s2 >> whnf (Inr $ Explicit (var n) s1)
  whnf t @ (Abs _) = return $ In $ Inl t
  whnf (App (In t1) t2) = do
    s <- get
    t1' <- whnf t1
    case t1' of
      In (Inl (Abs (In t))) -> withState (Cons $ explicit t2 s) $ whnf t
      _ -> return $ app t1' $ explicit t2 s

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

nf :: Whnf f => f (Expr ETerm) -> Subst (Expr ETerm) -> Expr ETerm
nf x s0 =
  let (In (Inl y), s) = runState (whnf x) s0 in
    case y of
      Abs (In a) -> lam $ nf a $ (explicit (var 0) Id) `Cons` (Comp s Shift)
      App a b -> f a b
        where
          f (In (Inl (App x y))) (In (Inr (Explicit (In a) s))) = f x y `app` nf a s
          f a (In (Inr (Explicit (In b) s))) = app a $ nf b s
      _ -> term y

reduce :: Expr ETerm -> Expr ETerm
reduce (In e) = nf e Id
