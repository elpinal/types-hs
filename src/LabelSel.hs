{-# LANGUAGE DeriveGeneric #-}

module LabelSel
  (
  ) where

import GHC.Generics

import Index

newtype Symbol = Symbol String
  deriving (Eq, Show)

data Label = Label Symbol Int
  deriving (Eq, Show)

sub :: Label -> Label
sub (Label s n) = Label s $ n - 1

newtype Variable = Variable Int
  deriving (Eq, Show)

data Term
  = Var Variable
  | Abs Label Term
  | App Label Term Term
  deriving (Eq, Show, Generic)

def :: Label
def = Label (Symbol "default") 0

abs :: Term -> Term
abs = Abs def

app :: Term -> Term -> Term
app = App def

reduce :: Term -> Term
reduce t @ (Var _) = t
reduce t @ (Abs _ _) = t
reduce (App l @ (Label s n) t1 t2) =
  case reduce t1 of
    Abs l' @ (Label s' n') t
      | l == l'   -> reduce $ substTop t2' t
      | s /= s'   -> Abs l' $ App l t $ shift 1 t2'
      | n < n'    -> Abs (sub l') $ App l t $ shift 1 t2'
      | otherwise -> Abs l' $ App (sub l) t $ shift 1 t2'
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

instance Shift Term

class Subst a where
  subst :: Int -> Term -> a -> a

instance Subst Term where
  subst n by = walk 0
    where
      walk c (Var v)
        | v == Variable (n + c) = shift c by
        | otherwise             = Var v
      walk c (Abs l t) = Abs l $ walk (c + 1) t
      walk c (App l t1 t2) = App l (walk c t1) (walk c t2)
