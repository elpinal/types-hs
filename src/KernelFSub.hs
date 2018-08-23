module KernelFSub
  ( Term(..)
  , Type(..)
  , typeOf
  , Context(..)
  , Binding(..)
  ) where

data Term
  = Var Int
  | Abs Type Term
  | App Term Term
  | TAbs Type Term
  | TApp Term Type

data Type
  = TVar Int
  | Top
  | Type :-> Type
  | Forall Type Type
  deriving (Eq, Show)

tymap :: (Int -> Int -> Type) -> Int -> Type -> Type
tymap f = walk
  where
    walk c (TVar n) = f c n
    walk _ Top = Top
    walk c (ty1 :-> ty2) = walk c ty1 :-> walk c ty2
    walk c (Forall ty1 ty2) = Forall (walk c ty1) (walk c ty2)

shiftAbove :: Int -> Int -> Type -> Type
shiftAbove c d = tymap (\c' n -> if n >= c' then TVar (n + d) else TVar n) c

shift :: Int -> Type -> Type
shift = shiftAbove 0

subst :: Int -> Type -> Type -> Type
subst j ty' = tymap (\c n -> if n == c + j then shift c ty' else TVar n) 0

substTop :: Type -> Type -> Type
substTop ty' ty = shift (-1) $ subst 0 (shift 1 ty') ty

data Binding
  = Term Type -- ^ @x:T@
  | Type Type -- ^ @X<:T@
  deriving Show

newtype Context = Context { getContext :: [Binding] }
  deriving Show

nth :: Context -> Int -> Either String Binding
nth (Context xs) n
  | n < length xs = return $ xs !! n
  | otherwise = Left $ "unbound variable: " ++ show n

append :: Context -> Binding -> Context
append (Context xs) x = Context $ x : xs

expose :: Context -> Type -> Either String Type
expose ctx (TVar n) = nth ctx n >>= f
  where
    f (Term _) = Left "unexpected error"
    f (Type ty) = expose ctx ty
expose _ ty = return ty

typeOf :: Context -> Term -> Either String Type
typeOf ctx (Var n) = nth ctx n >>= f
  where
    f (Term ty) = return ty
    f (Type _) = Left "unexpected error"
typeOf ctx (Abs ty t) = (ty :->) <$> typeOf (append ctx $ Term ty) t
typeOf ctx (App t1 t2) = do
  ty1 <- typeOf ctx t1 >>= expose ctx
  case ty1 of
    ty11 :-> ty12 -> do
      ty2 <- typeOf ctx t2
      isSubtypeOf ctx ty2 ty11
      return ty12
    _ -> Left "application of non-function"
typeOf ctx (TAbs ty t) = Forall ty <$> typeOf (append ctx $ Type ty) t
typeOf ctx (TApp t ty2) = do
  ty1 <- typeOf ctx t >>= expose ctx
  case ty1 of
    Forall ty11 ty12 -> do
      isSubtypeOf ctx ty2 ty11
      return $ substTop ty2 ty12
    _ -> Left "type application of non-polymorphic function"

isSubtypeOf :: Context -> Type -> Type -> Either String ()
isSubtypeOf _ _ Top = return ()
isSubtypeOf ctx (ty11 :-> ty12) (ty21 :-> ty22) = isSubtypeOf ctx ty21 ty11 >> isSubtypeOf ctx ty12 ty22
isSubtypeOf ctx (Forall u1 ty1) (Forall u2 ty2)
  | u1 == u2 = isSubtypeOf (append ctx $ Type u1) ty1 ty2
  | otherwise = Left "kernel F<: accepts only the limited rule for quantification"
isSubtypeOf _ (TVar m) (TVar n) | m == n = return ()
isSubtypeOf ctx (TVar n) ty1 = nth ctx n >>= f
  where
    f (Term _) = Left "unexpected error"
    f (Type ty2) = isSubtypeOf ctx ty2 ty1
isSubtypeOf _ ty1 ty2 = Left $ show ty1 ++ " is not subtype of " ++ show ty2
