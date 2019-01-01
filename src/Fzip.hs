{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
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
  deriving (Eq, Show)

newtype Variable = Variable Int
  deriving (Eq, Ord, Show)

newtype Context = Context [Binding]
  deriving (Eq, Show)

data Binding
  = Term Type
  | Universal
  | Existential
  | Def Type
  deriving (Eq, Show)

data TypeError
  = UnboundVariable Variable
  | TypeMismatch Type Type
  | NotFunction Type
  | NotExistential Type
  | NotPolymorphic Type
  | NotPure Context
  | NotTermBinding Binding
  | IllFormedOnPureContext Type Context
  deriving (Eq, Show)

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
      _ -> return ()

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

typecheck :: Context -> Term -> Either TypeError (Type, Context)
typecheck ctx = run . runError . runState ctx . typeOf

class Typed a where
  typeOf :: Members Env r => a -> Eff r Type

instance Typed Term where
  typeOf (Var v) = lookupVar v
