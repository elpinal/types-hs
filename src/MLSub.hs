{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MLSub
  ( infer
  , KindContext(..)
  , Context(..)
  , Term(..)
  , TI
  , runTI
  , typeOf
  , Subst(..)
  , Type(..)
  , Ident(..)
  , Kind(..)
  , PolyType(..)
  , Label(..)
  , Error(..)
  ) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Foldable
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set

newtype Kind = RecordKind { getRecordKind :: Map.Map Label Type }
  deriving (Eq, Show, Semigroup, Monoid)

-- | @union@ returns the right-biased union of two record kinds.
union :: Kind -> Kind -> Kind
union (RecordKind m1) (RecordKind m2) = RecordKind $ Map.union m2 m1

matchKind :: Kind -> Kind -> Constraints
matchKind (RecordKind m1) (RecordKind m2) = matchRecord m1 m2

matchRecord :: Map.Map Label Type -> Map.Map Label Type -> Constraints
matchRecord m1 m2 = Set.fromList $ Map.elems $ Map.intersectionWith Constr m1 m2

isUniversal :: Kind -> Bool
isUniversal = Map.null . getRecordKind

data Type
  = Int
  | TVar Ident
  | Type :-> Type
  | RecordType (Map.Map Label Type)
  deriving (Show, Eq, Ord)

newtype PolyType = PolyType { getPolyType :: (Map.Map Ident Kind, Type) }
  deriving (Eq, Show)

class Ftv a where
  ftv :: a -> Set.Set Ident

instance Ftv Kind where
  ftv = foldMap ftv . Map.elems . getRecordKind

instance Ftv Type where
  ftv Int = mempty
  ftv (TVar i) = Set.singleton i
  ftv (t1 :-> t2) = ftv t1 `Set.union` ftv t2
  ftv (RecordType m) = foldMap ftv $ Map.elems m

instance Ftv PolyType where
  ftv pt = (ftv (monotype pt) Set.\\ Map.keysSet (quantifiers pt)) <> foldMap ftv (Map.elems $ quantifiers pt)

-- | Essentially free type variables.
class Eftv a where
  eftv :: a -> TI (Set.Set Ident)

instance Eftv Kind where
  eftv (RecordKind m) = fmap mconcat . mapM eftv $ Map.elems m

instance Eftv Type where
  eftv ty = essential (show ty) $ ftv ty

instance Eftv PolyType where
  eftv pt = essential (show pt) $ ftv pt

essential :: String -> Set.Set Ident -> TI (Set.Set Ident)
essential s = loop
  where
    loop :: Set.Set Ident -> TI (Set.Set Ident)
    loop is = do
      kctx <- get
      is' <- foldrM (\i xs -> (xs <>) . ftv <$> kctx # i) is is `annotate` ("essentially free type variables for a type: " ++ s)
      if is == is'
        then return is
        else loop is'

instance Eftv Context where
  eftv = fmap mconcat . mapM eftv . getContext

quantifiers :: PolyType -> Map.Map Ident Kind
quantifiers = fst . getPolyType

monotype :: PolyType -> Type
monotype = snd . getPolyType

data Term
  = Var Int
  | Abs String Term
  | App Term Term
  | Let Term Term
  | Record (Map.Map Label Term)
  | Select Term Label
  deriving Show

newtype Ident = Ident Int
  deriving (Eq, Ord, Show)

newtype Label = Label String
  deriving (Eq, Ord, Show)

newtype Context = Context { getContext :: [PolyType] }
  deriving (Eq, Show)

nth :: Int -> Context -> TI PolyType
nth n (Context xs)
  | 0 <= n && n < length xs = return $ xs !! n
  | otherwise = throwError $ UnboundVariable n $ Context xs

push :: Context -> PolyType -> Context
push (Context xs) pt = Context $ pt : xs

pushMono :: Context -> Type -> Context
pushMono ctx t = push ctx $ PolyType (mempty, t)

instance Ftv Context where
  ftv = Set.unions . map ftv . getContext

newtype KindContext = KindContext { getKindContext :: Map.Map Ident Kind }
  deriving (Show, Eq)

mapKindContext :: (Map.Map Ident Kind -> Map.Map Ident Kind) -> KindContext -> KindContext
mapKindContext f = KindContext . f . getKindContext

(#) :: KindContext -> Ident -> TI Kind
(KindContext m) # i = maybe (throwError $ UnboundTypeVariable (KindContext m) i) return $ Map.lookup i m

update :: Ident -> Kind -> KindContext -> KindContext
update i k = mapKindContext $ Map.insert i k

-- | Returns the right-biased union of two kind contexts.
(+##) :: KindContext -> KindContext -> KindContext
(KindContext m1) +## (KindContext m2) = KindContext $ Map.union m2 m1

data Constr = Constr
  { lhs :: Type
  , rhs :: Type
  }
  deriving (Eq, Ord, Show)

instance Substitution Constr where
  apply s (Constr ty1 ty2) = apply s ty1 `Constr` apply s ty2

type Constraints = Set.Set Constr

(?=) :: Type -> Type -> Constraints
x ?= y = Set.singleton $ Constr x y

newtype Subst = Subst (Map.Map Ident Type)
  deriving (Eq, Show, Semigroup, Monoid)

(\\) :: Subst -> Set.Set Ident -> Subst
(Subst m) \\ is = Subst $ m `Map.withoutKeys` is

class Substitution a where
  apply :: Subst -> a -> a

instance Substitution Subst where
  apply w (Subst m) = Subst $ apply w <$> m

instance Substitution Type where
  apply _ Int = Int
  apply (Subst m) (TVar i) = Map.findWithDefault (TVar i) i m
  apply s (t1 :-> t2) = apply s t1 :-> apply s t2
  apply s (RecordType m) = RecordType $ apply s <$> m

instance Substitution PolyType where
  apply s (PolyType (m, ty)) = PolyType (m, apply (s \\ Map.keysSet m) ty)

instance Substitution Context where
  apply s (Context xs) = Context $ apply s <$> xs

instance Substitution Kind where
  apply s (RecordKind m) = RecordKind $ apply s <$> m

instance Substitution KindContext where
  apply s (KindContext m) = KindContext $ apply s <$> m

type TI = StateT KindContext (Counter (Except Error))

type Counter = StateT Int

data Error
  = Annotate String Error
  | RecordMismatch
  | RecursiveType
  -- |
  -- The structures of types does not match.
  -- Note that type variables can match *structurally* any types.
  | TypeStructureMismatch Type Type
  -- |
  -- A record and a non-record cannot be unified.
  -- More precisely, the type variable is kinded as a record, but the type cannot be a record.
  | TypeMismatchRecord Ident Type
  | UnboundVariable Int Context
  | UnboundTypeVariable KindContext Ident
  deriving (Eq, Show)

throwError :: Error -> TI a
throwError = lift . lift . throwE

annotate :: TI a -> String -> TI a
annotate a s = liftCatch (liftCatch catchE) a $ throwError . Annotate s

runTI :: TI a -> KindContext -> Either Error (a, KindContext)
runTI ti kctx = runExcept $ evalStateT (runStateT ti kctx) 0

typeOf :: TI (a, Type) -> KindContext -> Either Error (Type, KindContext)
typeOf ti kctx = do
  ((_, ty), kctx') <- runTI ti kctx
  return (ty, kctx')

infer :: Context -> Term -> TI (Subst, Type)
infer ctx t0 = case t0 of
  Var n -> do
    pt <- nth n ctx
    (s, kctx') <- (`runStateT` KindContext mempty) $
      Subst <$> (\k -> do
        i <- lift freshTVar
        bind i k
        return $ TVar i
      ) `traverse` quantifiers pt
    modify (+## apply s kctx')
    return (mempty, apply s $ monotype pt)
  Abs _ t -> do
    tv <- introduceFreshUniversal
    (s, ty) <- infer (pushMono ctx tv) t
    return (s, apply s tv :-> ty)
  App t1 t2 -> do
    (s1, ty1) <- infer ctx t1
    (s2, ty2) <- infer (apply s1 ctx) t2
    tv <- introduceFreshUniversal
    s' <- unify $ apply s2 ty1 ?= (ty2 :-> tv)
    return (s' @@ s2 @@ s1, apply s' tv)
  Let t1 t2 -> do
    (s1, ty1) <- infer ctx t1
    let ctx' = apply s1 ctx
    pt1 <- close ctx' ty1 `annotate` ("closing the type of a term (" ++ show t1 ++ ") which is rhs of let-binding")
    (s2, ty2) <- infer (push ctx' pt1) t2
    return (s2 @@ s1, ty2)
  Record m -> do
    (s, m') <- foldrM (inferField ctx) (mempty, mempty) $ Map.assocs m
    return (s, apply s $ RecordType m')
  Select t l -> do
    (s1, ty1) <- infer ctx t
    tv <- introduceFreshUniversal
    tvR <- introduceFresh $ RecordKind $ Map.singleton l tv
    s' <- unify $ ty1 ?= tvR
    return (s' @@ s1, apply s' tv)

introduceFreshUniversal :: TI Type
introduceFreshUniversal = introduceFresh mempty

introduceFresh :: Kind -> TI Type
introduceFresh k = do
  i <- freshTVar
  bind i k
  return $ TVar i

inferField :: Context -> (Label, Term) -> (Subst, Map.Map Label Type) -> TI (Subst, Map.Map Label Type)
inferField ctx (l, t) (s, m) = do
  (s', ty) <- infer (apply s ctx) t
  return (s' @@ s, Map.insert l ty m)

close :: Context -> Type -> TI PolyType
close ctx ty = do
  is <- eftv ty `annotate` ("closing " ++ show ty)
  is' <- eftv ctx `annotate` ("closing under context: " ++ show ctx)
  let xs = is Set.\\ is'
  qs <- gets $ (`Map.restrictKeys` xs) . getKindContext
  modify $ mapKindContext (`Map.withoutKeys` xs)
  return $ PolyType (qs, ty)

freshTVar :: TI Ident
freshTVar = do
  n <- lift get
  lift $ put $ n + 1
  return $ Ident n

unify :: Constraints -> TI Subst
unify e = execStateT (mapM_ f e) mempty
  where
    f :: Constr -> StateT Subst TI ()
    f c = gets (`apply` c) >>= lift . flip annotate ("unifying " ++ show c) . mgu >>= extSubst

mgu :: Constr -> TI Subst
mgu (Constr ty1 ty2)
  | ty1 == ty2 = return mempty
  | otherwise = case (ty1, ty2) of
      (ty11 :-> ty12, ty21 :-> ty22) -> unify $ ty11 ?= ty21 <> ty12 ?= ty22
      (RecordType m1, RecordType m2) | Map.keysSet m1 == Map.keysSet m2 -> unify $ matchRecord m1 m2
      (TVar i, t) -> varBind i t
      (t, TVar i) -> varBind i t
      _ -> throwError $ TypeStructureMismatch ty1 ty2

varBind :: Ident -> Type -> TI Subst
varBind i1 t = case t of
  TVar i2 -> do
    applyCtx $ i1 |-> t
    k1 <- getKind i1 `annotate` "varBind: both type variables: lhs"
    k2 <- getKind i2 `annotate` "varBind: both type variables: rhs"
    bind i2 $ union k1 k2
    fmap (@@ (i1 |-> t)) $ unify $ matchKind k1 k2
  RecordType m2 -> do
    occurCheck i1 t
    applyCtx $ i1 |-> t
    m1 <- getRecordKind <$> getKind i1 `annotate` "varBind: type variable and record type"
    fmap (@@ (i1 |-> t)) $ f m1 >>= unify . Set.fromList . Map.elems
      where
        f = Map.traverseWithKey $ \l x -> maybe (throwError RecordMismatch) (return . Constr x . apply (i1 |-> t)) $ Map.lookup l m2
  _ -> do
    occurCheck i1 t
    k <- getKind i1 `annotate` "varBind: type variable to be non-record"
    unless (isUniversal k) $
      throwError $ TypeMismatchRecord i1 t
    applyCtx $ i1 |-> t
    return $ i1 |-> t

occurCheck :: Ident -> Type -> TI ()
occurCheck i ty = when (i `Set.member` ftv ty) $ throwError RecursiveType

(|->) :: Ident -> Type -> Subst
i |-> ty = Subst $ Map.singleton i ty

extSubst :: Monad m => Subst -> StateT Subst m ()
extSubst s = modify (s @@)

infixr 9 @@
(@@) :: Subst -> Subst -> Subst
(Subst m1) @@ (Subst m2) = Subst $ fmap (apply $ Subst m1) m2 `Map.union` m1

getKind :: Ident -> TI Kind
getKind i = get >>= (# i)

applyCtx :: Subst -> TI ()
applyCtx = modify . apply

bind :: Monad m => Ident -> Kind -> StateT KindContext m ()
bind i k = modify $ update i k
