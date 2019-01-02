{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}

module Fzip
  ( Term(..)
  , Variable(..)
  , Label(..)
  , Record(..)
  , Type(..)

  , Context(..)
  , Binding(..)

  , TypeError(..)

  , typecheck
  ) where

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.State
import Data.Coerce
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set

import GHC.Generics

import Index

newtype Label = Label String
  deriving (Eq, Show)

newtype Record a = Record (Map.Map Label a)
  deriving (Eq, Show, Foldable, Functor)

data Term
  = Var Variable
  | Abs Type Term
  | App Term Term
  | Let Term Term
  | TmRecord (Record Term)
  | Proj Term Label
  | Poly Term
  | Inst Term Type
  | Open Variable Term
  | Restrict Term
  | Coerce Term Type
  | Exists Term
  | WitDef Variable Type Term
  deriving (Eq, Show)

data Type
  = IntType
  | Type :-> Type
  | TVar Variable
  | Forall Type
  | Some Type
  | TRecord (Record Type)
  deriving (Eq, Show, Generic)

infixr 0 :->

newtype Variable = Variable Int
  deriving (Eq, Ord, Show)
  deriving Shift via IndexedVariable

newtype Context = Context { getContext :: [Binding] }
  deriving (Eq, Show)

data Binding
  = Term Type
  | Universal
  | Existential
  | Def Type

  | Consumed
  | Forbidden
  deriving (Eq, Show, Generic)

data TypeError
  = UnboundVariable Variable
  | TypeMismatch Type Type
  | NotFunction Type
  | NotExistential Type
  | NotPolymorphic Type
  | NotPure Context
  | NotTermBinding Binding
  | NotTypeBinding Binding
  | NotExistentialBinding Binding
  | IllFormedOnPureContext Type Context
  | ForbiddenVariable Variable
  deriving (Eq, Show)

instance Shift Binding

instance Shift Type where
  shiftAbove c d (Forall ty) = Forall $ shiftAbove (c + 1) d ty
  shiftAbove c d (Some ty)   = Some $ shiftAbove (c + 1) d ty
  shiftAbove c d ty          = to $ gShiftAbove c d $ from ty

instance Shift a => Shift (Record a) where
  shiftAbove c d (Record m) = Record $ shiftAbove c d <$> m

instance Shift Context where
  shiftAbove c d (Context bs) = Context $ shiftAbove c d <$> bs

subst :: Int -> Type -> Type -> Type
subst j by = walk 0
  where
    walk _ IntType       = IntType
    walk c (ty1 :-> ty2) = walk c ty1 :-> walk c ty2
    walk c ty @ (TVar (Variable n))
      | n == j + c = shift c by
      | otherwise  = ty
    walk c (Forall ty) = Forall $ walk (c + 1) ty
    walk c (Some ty)   = Some $ walk (c + 1) ty
    walk c (TRecord r) = TRecord $ walk c <$> r

drop0 :: Set.Set Variable -> Set.Set Variable
drop0 = Set.mapMonotonic (Variable . subtract 1 . coerce) . Set.delete (Variable 0)

ftv :: Type -> Set.Set Variable
ftv IntType       = mempty
ftv (ty1 :-> ty2) = ftv ty1 <> ftv ty2
ftv (TVar v)      = Set.singleton v
ftv (Forall ty)   = drop0 $ ftv ty
ftv (Some ty)     = drop0 $ ftv ty
ftv (TRecord r)   = foldMap ftv r

isPure :: Context -> Bool
isPure (Context bs) = all f bs
  where
    f Existential = False
    f _ = True

nth :: Member (Error TypeError) r => Variable -> Context -> Eff r Binding
nth v @ (Variable n) (Context bs)
  | 0 <= n && n < length bs = return $ bs !! n
  | otherwise               = throwError $ UnboundVariable v

fromTermBinding :: Member (Error TypeError) r => Binding -> Eff r Type
fromTermBinding (Term ty) = return ty
fromTermBinding b         = throwError $ NotTermBinding b

split :: Member (Error TypeError) r => Variable -> Context -> Eff r (Context, Binding, Context)
split v @ (Variable n) (Context bs)
  | 0 <= n && n < length bs = return (Context $ take n bs, bs !! n, shift (-n') $ Context $ drop n' bs)
  | otherwise               = throwError $ UnboundVariable v
    where n' = n + 1

wfPure :: Members Env r => Type -> Eff r ()
wfPure ty = do
  ctx <- get
  forM_ (ftv ty) $ \v -> do
    b <- nth v ctx
    case b of
      Existential -> throwError $ IllFormedOnPureContext ty ctx
      Def ty'     -> wfPure ty'
      Universal   -> return ()
      Term _      -> throwError $ NotTypeBinding b
      Forbidden   -> throwError $ ForbiddenVariable v

type Env = '[State Context, Error TypeError]

pureCtx :: Members Env r => Eff r ()
pureCtx = do
  ctx <- get
  unless (isPure ctx) $
    throwError $ NotPure ctx

lookupVar :: Members Env r => Variable -> Eff r Type
lookupVar v = do
  ctx <- get
  ty <- nth v ctx >>= fromTermBinding
  wfPure ty
  return ty

insert :: Member (State Context) r => Binding -> Eff r ()
insert b = modify $ \(Context bs) -> shift 1 $ Context $ b : bs

pop :: Member (State Context) r => Eff r ()
pop = modify $ \(Context (_ : bs)) -> shift (-1) $ Context bs

typecheck :: Context -> Term -> Either TypeError (Type, Context)
typecheck ctx = run . runError . runState ctx . typeOf

class Typed a where
  typeOf :: Members Env r => a -> Eff r Type

instance Typed Term where
  typeOf (Var v) = lookupVar v
  typeOf (Abs ty1 t) = do
    wfPure ty1
    insert $ Term ty1
    ty2 <- typeOf t
    pop
    return $ ty1 :-> shift (-1) ty2
  typeOf (App t1 t2) = do
    ty1 <- typeOf t1
    ty2 <- typeOf t2
    case ty1 of
      ty11 :-> ty12
        | ty11 == ty2 -> return ty12
        | otherwise   -> throwError $ TypeMismatch ty11 ty2
      _ -> throwError $ NotFunction ty1
  typeOf (Let t1 t2) = do -- FIXME
    ty1 <- typeOf t1
    insert $ Term ty1
    ty2 <- typeOf t2
    pop
    return ty2
  typeOf (Exists t) = do
    insert Existential
    ty <- typeOf t
    -- ?
    return $ Some ty
  typeOf (Open v t) = do
    ctx <- get
    (ctx1, b, ctx2) <- split v ctx
    case b of
      Existential -> return ()
      _ -> throwError $ NotExistentialBinding b
    put ctx2
    ty <- typeOf t
    let n = length $ getContext ctx1
    case shift n ty of
      Some ty' -> do
        insert Consumed
        mapM_ insert $ reverse $ coerce ctx1
        return $ subst 0 (TVar $ Variable n) ty'
      _ -> throwError $ NotExistential ty
