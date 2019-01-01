{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
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
  deriving (Eq, Show, Foldable)

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

newtype Context = Context [Binding]
  deriving (Eq, Show)

data Binding
  = Term Type
  | Universal
  | Existential
  | Def Type
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
  | IllFormedOnPureContext Type Context
  deriving (Eq, Show)

instance Shift Binding

instance Shift Type where
  shiftAbove c d (Forall ty) = Forall $ shiftAbove (c + 1) d ty
  shiftAbove c d (Some ty) = Some $ shiftAbove (c + 1) d ty
  shiftAbove c d ty = to $ gShiftAbove c d $ from ty

instance Shift Variable where
  shiftAbove c d v @ (Variable n)
    | c <= n    = Variable $ n + d
    | otherwise = v

instance Shift a => Shift (Record a) where
  shiftAbove c d (Record m) = Record $ shiftAbove c d <$> m

instance Shift Context where
  shiftAbove c d (Context bs) = Context $ shiftAbove c d <$> bs

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
fromTermBinding b = throwError $ NotTermBinding b

wfPure :: Members Env r => Type -> Eff r ()
wfPure ty = do
  ctx <- get
  let vs = ftv ty
  forM_ vs $ \v -> do
    b <- nth v ctx
    case b of
      Existential -> throwError $ IllFormedOnPureContext ty ctx
      Def ty' -> wfPure ty'
      Universal -> return ()
      Term _ -> throwError $ NotTypeBinding b

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
