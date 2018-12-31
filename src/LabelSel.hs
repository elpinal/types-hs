{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module LabelSel
  (
  ) where

import GHC.Generics

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader
import Data.Coerce
import Data.List hiding (union)
import qualified Data.Map.Lazy as Map
import Data.Monoid

import Index

newtype Symbol = Symbol String
  deriving (Eq, Ord)

instance Show Symbol where
  show (Symbol s) = s

data Label = Label Symbol Int
  deriving (Eq, Ord)

instance Show Label where
  show (Label s n) = "?" ++ show s ++ show n

sub :: Label -> Label
sub (Label s n) = Label s $ n - 1

newtype Variable = Variable Int
  deriving Eq

instance Show Variable where
  show (Variable n) = "v" ++ show n

data Term
  = Var Variable
  | Abs Label (Fixed Type) Term
  | App Label Term Term
  deriving (Eq, Generic)

instance Show Term where
  showsPrec n (Var v) = shows v
  showsPrec n (Abs l ty t) = showParen (n >= 10) $ showString "lam " . shows l . showString " : " . shows ty . showString ". " . showsPrec n t
  showsPrec n (App l t1 t2) = showParen (n > 10) $ showsPrec 10 t1 . showString " " . shows l . showString " " . showsPrec 11 t2

var :: Int -> Term
var = Var . Variable

def :: Label
def = Label (Symbol "_") 1

abs_ :: Type -> Term -> Term
abs_ = Abs def . Fixed

app :: Term -> Term -> Term
app = App def

data Base
  = Int
  | Bool
  deriving Eq

instance Show Base where
  show Int = "int"
  show Bool = "bool"

data Type
  = Base Base
  | Record :-> Base
  deriving Eq

infixr 3 :->

instance Show Type where
  showsPrec n (Base b) = showsPrec n b
  showsPrec n (r :-> b) = showParen (n > 3) $ showsPrec 4 r . showString " -> " . showsPrec 3 b

newtype Record = Record (Map.Map Label Type)
  deriving (Eq, Semigroup, Monoid)

instance Show Record where
  showsPrec _ (Record m) = showChar '{' . h . showChar '}'
    where
      h = appEndo $ foldMap Endo $ intersperse id $ map (\(l, ty) -> shows l . showString " => " . shows ty) $ Map.assocs m

union :: Record -> Record -> Record
union (Record m) = coerce $ Map.union m

free :: Record -> Symbol -> Int -> Int
free (Record m) s n = minimum [ i | i <- [1, 2 ..], i - f i == n]
  where
    f i = Map.size $ Map.filterWithKey (\(Label s' j) _ -> s' == s && j <= i) m

adjust :: Record -> Record -> Record
adjust r (Record m) = Map.foldrWithKey f mempty m
  where
    f :: Label -> Type -> Record -> Record
    f (Label s n) = coerce . Map.insert (Label s $ free r s n)

concatR :: Record -> Record -> Record
concatR r s = r `union` adjust r s

skip :: Record -> Symbol -> Int -> Int
skip (Record m) s n = n - f n
  where
    f i = Map.size $ Map.filterWithKey (\(Label s' j) _ -> s' == s && j <= i) m

match :: Record -> Record -> Record
match r (Record m) = Map.foldrWithKey f mempty m
  where
    f :: Label -> Type -> Record -> Record
    f (Label s n) = coerce . Map.insert (Label s $ skip r s n)

reduce :: Term -> Term
reduce t @ (Var _) = t
reduce t @ (Abs _ _ _) = t
reduce (App l @ (Label s n) t1 t2) =
  case reduce t1 of
    Abs l' @ (Label s' n') ty t
      | l == l'   -> reduce $ substTop t2' t
      | s /= s'   -> Abs l' ty $ App l t $ shift 1 t2'
      | n < n'    -> Abs (sub l') ty $ App l t $ shift 1 t2'
      | otherwise -> Abs l' ty $ App (sub l) t $ shift 1 t2'
    t1' -> App l t1' $ reduce t2'
  where t2' = reduce t2

substTop :: Term -> Term -> Term
substTop by t = shift (-1) $ subst 0 (shift 1 by) t

instance Shift Variable where
  shiftAbove c d v @ (Variable n)
    | c <= n    = Variable $ n + d
    | otherwise = v

instance Shift Label where
  shiftAbove _ _ l = l

instance Shift Term where
  shiftAbove c d (Abs l ty t) = Abs l ty $ shiftAbove (c + 1) d t
  shiftAbove c d t = to $ gShiftAbove c d $ from t

class Subst a where
  subst :: Int -> Term -> a -> a

instance Subst Term where
  subst n by = walk 0
    where
      walk c (Var v)
        | v == Variable (n + c) = shift c by
        | otherwise             = Var v
      walk c (Abs l ty t) = Abs l ty $ walk (c + 1) t
      walk c (App l t1 t2) = App l (walk c t1) (walk c t2)

newtype Context = Context [Type]
  deriving (Eq, Show)

add :: Type -> Context -> Context
add ty (Context xs) = Context $ ty : xs

data TypeError
  = UnboundVariable Int
  | NotFunction Type
  | TypeMismatch Type Type
  | UnboundLabel Label
  deriving (Eq, Show)

class Typed a where
  typeOf :: Members '[Reader Context, Error TypeError] r => a -> Eff r Type

instance Typed Variable where
  typeOf (Variable n) = do
    Context xs <- ask
    if 0 <= n && n < length xs
      then return $ xs !! n
      else throwError $ UnboundVariable n

separate :: Member (Error TypeError) r => Label -> Record -> Eff r (Type, Record)
separate l (Record m) =
  case Map.lookup l m of
    Nothing -> throwError $ UnboundLabel l
    Just ty -> return (ty, Record $ Map.delete l m)

instance Typed Term where
  typeOf (Var v) = typeOf v
  typeOf (Abs l (Fixed ty) t) = do
    ty' <- local (add ty) $ typeOf t
    case ty' of
      r :-> b -> return $ concatR (Record $ Map.singleton l ty) r :-> b
      Base b -> return $ Record (Map.singleton l ty) :-> b
  typeOf (App l t1 t2) = do
    ty1 <- typeOf t1
    ty2 <- typeOf t2
    case ty1 of
      r :-> b -> do
        (ty, s) <- separate l r
        when (ty /= ty2) $
          throwError $ TypeMismatch ty ty2
        return $ match (Record $ Map.singleton l ty) s :-> b
      _ -> throwError $ NotFunction ty1
