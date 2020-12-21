{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Types where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.State

-- A Term is a lambda term
data Term
  = Ann Term (CType 'Polytype)
  | Var TmName
  | Unit
  | App Term Term
  | Abs Term
  deriving (Show, Eq)

data TypeCategory = Monotype | Polytype
  deriving (Show, Eq)

data CType :: TypeCategory -> * where
  TyArrow :: CType a -> CType a -> CType a
  TyUnit :: CType a
  TyVar :: TyName -> CType a
  TyExists :: FreeName -> CType a
  TyForall :: CType 'Polytype -> CType 'Polytype

deriving instance Show (CType a)

deriving instance Eq (CType a)

ctypeToPoly :: CType a -> CType 'Polytype
ctypeToPoly (TyArrow ty1 ty2) = TyArrow (ctypeToPoly ty1) (ctypeToPoly ty2)
ctypeToPoly TyUnit = TyUnit
ctypeToPoly (TyVar n) = TyVar n
ctypeToPoly (TyExists n) = TyExists n
ctypeToPoly (TyForall ty) = TyForall ty

ctypeToMono :: CType a -> Maybe (CType 'Monotype)
ctypeToMono (TyArrow ty1 ty2) = liftA2 TyArrow (ctypeToMono ty1) (ctypeToMono ty2)
ctypeToMono TyUnit = Just TyUnit
ctypeToMono (TyVar n) = Just (TyVar n)
ctypeToMono (TyExists n) = Just (TyExists n)
ctypeToMono (TyForall _) = Nothing

subst :: TmName -> Term -> Term -> Term
subst i tm1 (Ann tm2 ty) = Ann (subst i tm1 tm2) ty
subst i tm1 (Abs tm2) = Abs (subst (addTmName i 1) tm1 tm2)
subst i tm (Var j) = if i == j then tm else Var j
subst i tm (App tm1 tm2) = App (subst i tm tm1) (subst i tm tm2)
subst _ _ Unit = Unit

typeSubst :: TyName -> CType a -> CType a -> CType a
typeSubst i ty' (TyArrow ty1 ty2) = TyArrow (typeSubst i ty' ty1) (typeSubst i ty' ty2)
typeSubst _ _ TyUnit = TyUnit
typeSubst i ty' (TyVar n) =
  if i == n
    then ty'
    else TyVar n
typeSubst i ty' (TyExists n) =
  if i == TyN n
    then ty'
    else TyExists n
typeSubst i ty' (TyForall ty1) =
  case i of
    (TyI n) -> TyForall (typeSubst (TyI (n + 1)) ty' ty1)
    _ -> TyForall (typeSubst i ty' ty1)

newtype TmIdx = TmIdx Int
  deriving (Show, Eq, Num)

newtype TyIdx = TyIdx Int
  deriving (Show, Eq, Num)

newtype FreeName = FreeName Int
  deriving (Show, Eq, Num, Ord)

data TmName = TmI TmIdx | TmN FreeName
  deriving (Show, Eq)

data TyName = TyI TyIdx | TyN FreeName
  deriving (Show, Eq)

addTmName :: TmName -> Int -> TmName
addTmName (TmI tmIdx) i = TmI (tmIdx + TmIdx i)
addTmName (TmN tmn) i = TmN (tmn + FreeName i)

addTyName :: TyName -> Int -> TyName
addTyName (TyI tyIdx) i = TyI (tyIdx + TyIdx i)
addTyName (TyN tyn) i = TyN (tyn + FreeName i)

data CtxElem
  = CtxForall FreeName
  | CtxVar FreeName (CType 'Polytype)
  | CtxExist FreeName
  | CtxExistSolved FreeName (CType 'Monotype)
  | CtxMarker FreeName
  deriving (Show, Eq)

type Context = [CtxElem]

-- Replace a specific context element with a new possibly larger context
replaceCtxExistWith :: Context -> CtxElem -> Context -> Context
replaceCtxExistWith ctx e toInsert =
  let (l, r) = breakMarker e ctx
   in r ++ toInsert ++ l

-- Find a context element, drop it and split the context on it
breakMarker :: CtxElem -> Context -> (Context, Context)
breakMarker m ctx = let (l, _ : r) = break (== m) ctx in (r, l)

data ScopeState = ScopeState
  { termIdx :: TmIdx,
    typeIdx :: TyIdx,
    freeCount :: FreeName,
    context :: Context
  }
  deriving (Show, Eq)

-- Type alias for the State monad
type ScopeGen a = State ScopeState a

dropMarker :: CtxElem -> ScopeGen ()
dropMarker m = do
  ctx <- gets context
  let ctx' = tail $ dropWhile (/= m) ctx
  modify (\s -> s {context = ctx'})
