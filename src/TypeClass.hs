{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeClass
  ( reconstruct
  , recon
  , Expr(..)
  , Type(..)
  , Ident(..)
  , Assump(..)
  , Subst(..)
  , Pred(..)
  , Scheme(..)
  , scheme
  , Class(..)
  , Qual(..)
  , TypeError(..)
  ) where

import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.State
import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map

data Expr
  = Var Int
  | Abs Expr
  | App Expr Expr
  | Let Expr Expr
  deriving (Eq, Show)

data Scheme = Scheme (Set.Set Ident) Qual
  deriving (Eq, Show)

data Qual = Qual (Set.Set Pred) Type
  deriving (Eq, Show)

newtype Ident = Ident Int
  deriving (Eq, Ord, Show)

infixr 9 :->

data Type
  = TVar Ident
  | Type :-> Type
  | Int
  deriving (Eq, Ord, Show)

newtype Assump = Assump [Scheme]
  deriving (Eq, Show)

mapAssump :: ([Scheme] -> [Scheme]) -> Assump -> Assump
mapAssump f (Assump xs) = Assump $ f xs

data Pred = Type :< Class
  deriving (Eq, Ord, Show)

newtype Class = Class String
  deriving (Eq, Ord, Show)

data TypeError
  = Recursive Ident Type
  | NoUnifier Type Type
  | UnboundVariable Int
  deriving (Eq, Show)

newtype Subst = Subst (Map.Map Ident Type)
  deriving (Eq, Show)

emptySubst :: Subst
emptySubst = Subst mempty

(|->) :: Ident -> Type -> Subst
i |-> ty = Subst $ Map.singleton i ty

class Substitution a where
  apply :: Subst -> a -> a

instance Substitution Type where
  apply _ Int = Int
  apply s (t1 :-> t2) = apply s t1 :-> apply s t2
  apply (Subst m) ty @ (TVar i) = Map.findWithDefault ty i m

instance Substitution Pred where
  apply s (ty :< c) = apply s ty :< c

class Ftv a where
  ftv :: a -> Set.Set Ident

instance Ftv Type where
  ftv Int = mempty
  ftv (ty1 :-> ty2) = ftv ty1 <> ftv ty2
  ftv (TVar i) = Set.singleton i

instance Ftv Qual where
  ftv (Qual p ty) = foldMap ftv p <> ftv ty

instance Ftv Pred where
  ftv (ty :< _) = ftv ty

instance Ftv Scheme where
  ftv (Scheme is q) = ftv q Set.\\ is

instance Ftv Assump where
  ftv (Assump m) = foldMap ftv m

scheme :: Type -> Scheme
scheme = Scheme mempty . Qual mempty

local :: Member (State Assump) r => Scheme -> Eff r a -> Eff r a
local ty e = do
  modify $ mapAssump (ty :)
  x <- e
  modify $ mapAssump tail -- unsafe; be careful.
  return x

fresh :: Member (State Ident) r => Eff r Ident
fresh = do
  Ident n <- get
  put $ Ident $ n + 1
  return $ Ident n

freshTVar :: Member (State Ident) r => Eff r Type
freshTVar = TVar <$> fresh

assump :: Members '[State Assump, Error TypeError] r => Int -> Eff r Scheme
assump n = do
  Assump xs <- get
  if 0 <= n && n < length xs
    then return $ xs !! n
    else throwError $ UnboundVariable n

reconstruct :: Assump -> Expr -> Either TypeError (Type, Set.Set Pred)
reconstruct a e = run $ runError $ evalState a $ evalState (Ident 0) $ evalState emptySubst $ recon e

recon :: Members '[State Assump, State Subst, State Ident, Error TypeError] r => Expr -> Eff r (Type, Set.Set Pred)
recon (Var n) = do
  Scheme is (Qual p ty) <- assump n
  s <- fmap Subst $ sequence $ Map.fromSet (const freshTVar) is
  return (apply s ty, Set.map (apply s) p)
recon (Abs e) = do
  ty1 <- freshTVar
  (ty2, p) <- local (scheme ty1) $ recon e
  s <- get
  return (apply s ty1 :-> ty2, p)
recon (App e1 e2) = do
  (ty1, p) <- recon e1
  (ty2, q) <- recon e2
  tyR <- freshTVar
  s <- get
  u <- unify (apply s ty1) $ ty2 :-> tyR
  return (apply u tyR, Set.map (apply u) $ Set.map (apply s) p <> q)
recon (Let e1 e2) = do
  (ty1, p) <- recon e1
  tyS <- close $ Qual p ty1
  local tyS $ recon e2

close :: Members '[State Assump] r => Qual -> Eff r Scheme
close q = do
  Assump a <- get
  return $ Scheme (ftv q Set.\\ ftv (Assump a)) q

unify :: Members '[Error TypeError] r => Type -> Type -> Eff r Subst
unify ty1 ty2 | ty1 == ty2 = return emptySubst
unify (TVar i) ty = varBind i ty
unify ty (TVar i) = varBind i ty
unify (ty11 :-> ty12) (ty21 :-> ty22) = do
  s <- unify ty11 ty21
  t <- unify (apply s ty12) (apply s ty22)
  return $ t @@ s
unify ty1 ty2 = throwError $ NoUnifier ty1 ty2

varBind :: Members '[Error TypeError] r => Ident -> Type -> Eff r Subst
varBind i ty
  | TVar i == ty             = return emptySubst
  | i `Set.notMember` ftv ty = return $ i |-> ty
  | otherwise                = throwError $ Recursive i ty

(@@) :: Subst -> Subst -> Subst
s1 @ (Subst m1) @@ (Subst m2) = Subst $ fmap (apply s1) m2 `Map.union` m1
