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
  ) where

data Expr f = In (f (Expr f))

data Term a
  = Var
  | Abs a
  | App a a

term :: Term (Expr ETerm) -> Expr ETerm
term = In . Inl

var :: Expr ETerm
var = term Var

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
  fmap _ Var = Var
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
  render Var = "0"
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
