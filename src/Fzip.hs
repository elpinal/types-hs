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
  , Problem(..)
  , Reason(..)
  , fromProblem

  , typecheck
  ) where

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.State
import Data.Coerce
import Data.Functor
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.Map.Lazy as Map
import Data.Monoid
import qualified Data.Set as Set

import GHC.Generics

import Index

newtype Label = Label String
  deriving (Eq, Ord, Show)
  deriving Shift via Fixed Label

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
  deriving (Eq, Show, Generic)

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

data TypeError = TypeError [Reason] Problem
  deriving (Eq, Show)

data Problem
  = UnboundVariable Variable
  | UnboundLabel Label
  | TypeMismatch Type Type
  | NotFunction Type
  | NotExistential Type
  | NotPolymorphic Type
  | NotRecord Type
  | NotPure Context
  | NotTermBinding Binding
  | NotTypeBinding Binding
  | NotExistentialBinding Binding
  | IllFormedOnPureContext Type Context
  | ForbiddenVariable Variable
  | ExistentialLeak Type
  deriving (Eq, Show)

data Reason
  = TypeCheckingVariable
  | InContext Context
  deriving (Eq, Show)

throwProblem :: Member (Error TypeError) r => Problem -> Eff r a
throwProblem = throwError . TypeError []

fromProblem :: TypeError -> Problem
fromProblem (TypeError _ p) = p

instance Shift Binding

instance Shift Term where
  shiftAbove c d (Abs ty t)      = Abs (shiftAbove c d ty) $ shiftAbove (c + 1) d t
  shiftAbove c d (Let t1 t2)     = Let (shiftAbove c d t1) $ shiftAbove c d t2
  shiftAbove c d (Poly t)        = Poly $ shiftAbove (c + 1) d t
  shiftAbove c d (Restrict t)    = Restrict $ shiftAbove (c + 1) d t
  shiftAbove c d (Exists t)      = Exists $ shiftAbove (c + 1) d t
  shiftAbove c d (WitDef v ty t) = WitDef (shiftAbove c d v) (shiftAbove c d ty) $ shiftAbove (c + 1) d t
  shiftAbove c d t               = to $ gShiftAbove c d $ from t

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
  | otherwise               = throwProblem $ UnboundVariable v

fromTermBinding :: Member (Error TypeError) r => Binding -> Eff r Type
fromTermBinding (Term ty) = return ty
fromTermBinding b         = throwProblem $ NotTermBinding b

split :: Member (Error TypeError) r => Variable -> Context -> Eff r (Context, Binding, Context)
split v @ (Variable n) (Context bs)
  | 0 <= n && n < length bs = return (Context $ take n bs, bs !! n, shift (-n') $ Context $ drop n' bs)
  | otherwise               = throwProblem $ UnboundVariable v
    where n' = n + 1

wfPure :: Members Env r => Type -> Eff r ()
wfPure ty = do
  ctx <- get
  forM_ (ftv ty) $ \v -> do
    b <- nth v ctx
    case b of
      Existential -> throwProblem $ IllFormedOnPureContext ty ctx
      Def ty'     -> wfPure ty'
      Universal   -> return ()
      Term _      -> throwProblem $ NotTypeBinding b
      Forbidden   -> throwProblem $ ForbiddenVariable v
      Consumed    -> error $ "[bug] unexpected consumed type variable: " ++ show v

type Env = '[State Context, Error TypeError]

pureCtx :: Members Env r => Eff r ()
pureCtx = do
  ctx <- get
  unless (isPure ctx) $
    throwProblem $ NotPure ctx

lookupVar :: Members Env r => Variable -> Eff r Type
lookupVar v = do
  ctx <- get
  f ctx `ann` InContext ctx
  where
    f ctx = do
      ty <- nth v ctx >>= fromTermBinding
      wfPure ty
      return ty

insert :: Member (State Context) r => Binding -> Eff r ()
insert b = modify $ \(Context bs) -> shift 1 $ Context $ b : bs

insertWithoutShift :: Member (State Context) r => Context -> Eff r ()
insertWithoutShift (Context cs) = modify $ \(Context bs) -> Context $ cs ++ bs

pop :: Member (State Context) r => Eff r ()
pop = modify $ \(Context (_ : bs)) -> shift (-1) $ Context bs

makeConsumedUniversal :: Member (State Context) r => Eff r [Int]
makeConsumedUniversal = makeConsumedBinding Universal

makeConsumedForbidden :: Member (State Context) r => Eff r [Int]
makeConsumedForbidden = makeConsumedBinding Forbidden

makeConsumedBinding :: Member (State Context) r => Binding -> Eff r [Int]
makeConsumedBinding b0 = do
  Context bs <- get
  let (bs', ns) = run $ runState [] $ evalState (0 :: Int) $ f bs
  put $ Context bs'
  return ns
  where
    f :: Members '[State Int, State [Int]] r => [Binding] -> Eff r [Binding]
    f []       = return []
    f (b : bs) = do
      n <- get
      modify (+ (1 :: Int))
      bs' <- f bs
      case b of
        Consumed -> modify ((n :: Int) :) $> (b0 : bs')
        _        -> return $ b : bs'

makeConsumed :: Member (State Context) r => [Int] -> Eff r ()
makeConsumed ns = do
  Context bs <- get
  put $ Context $ f bs
  where
    f bs =
      let m = IntMap.fromAscList $ zip [0 ..] bs in
      let g = appEndo $ foldMap Endo $ IntMap.adjust (const Consumed) <$> ns in
        IntMap.elems $ g m

lookupLabel :: Member (Error TypeError) r => Label -> Record a -> Eff r a
lookupLabel l (Record m) = maybe (throwProblem $ UnboundLabel l) return $ Map.lookup l m

typecheck :: Context -> Term -> Either TypeError (Type, Context)
typecheck ctx = run . runError . runState ctx . typeOf

ann :: Member (Error TypeError) r => Eff r a -> Reason -> Eff r a
ann m r = m `catchError` \(TypeError rs p) -> throwError $ TypeError (r : rs) p

class Typed a where
  typeOf :: Members Env r => a -> Eff r Type

instance Typed Term where
  typeOf (Var v) = lookupVar v `ann` TypeCheckingVariable
  typeOf (Abs ty1 t) = do
    wfPure ty1
    insert $ Term ty1
    ty2 <- typeOf t
    pop
    return $ ty1 :-> shift (-1) ty2
  typeOf (App t1 t2) = do
    ty1 <- typeOf t1
    xs <- makeConsumedForbidden
    ty2 <- typeOf t2
    makeConsumed xs
    case ty1 of
      ty11 :-> ty12
        | ty11 == ty2 -> return ty12
        | otherwise   -> throwProblem $ TypeMismatch ty11 ty2
      _ -> throwProblem $ NotFunction ty1
  typeOf (Let t1 t2) = do
    ty1 <- typeOf t1
    xs <- makeConsumedUniversal
    insert $ Term ty1
    ty2 <- typeOf t2
    pop
    makeConsumed xs
    return $ shift (-1) ty2
  typeOf (Exists t) = do
    insert Existential
    ty <- typeOf t
    pop
    return $ Some ty
  typeOf (Open v t) = do
    ctx <- get
    (ctx1, b, ctx2) <- split v ctx
    case b of
      Existential -> return ()
      _ -> throwProblem $ NotExistentialBinding b
    put ctx2
    let n = length $ getContext ctx1
    ty <- typeOf $ shift ((-n) - 1) t
    case shift n ty of
      Some ty' -> do
        insert Consumed
        modify $ \ctx0 -> shift n (ctx0 :: Context)
        insertWithoutShift ctx1
        return $ subst 0 (TVar $ Variable n) ty'
      _ -> throwProblem $ NotExistential ty
  typeOf (Restrict t) = do
    insert Existential
    ty <- typeOf t
    when (Variable 0 `Set.member` ftv ty) $
      throwProblem $ ExistentialLeak ty
    pop
    return $ shift (-1) ty
  typeOf (Proj t l) = do
    ty <- typeOf t
    case ty of
      TRecord r -> lookupLabel l r
      _         -> throwProblem $ NotRecord ty
