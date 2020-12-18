{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module TypeChecker where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.State

newtype TmIdx = TmIdx Int
  deriving (Show, Eq, Num)

newtype TyIdx = TyIdx Int
  deriving (Show, Eq, Num)

newtype FreeName = FreeName Int
  deriving (Show, Eq, Num)

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

-- The state of indices and free names generate
data ScopeState = ScopeState
  { termIdx :: TmIdx,
    typeIdx :: TyIdx,
    freeCount :: FreeName,
    context :: Context
  }
  deriving (Show, Eq)

-- Type alias for the State monad
type ScopeGen a = State ScopeState a

data TypeCategory = Monotype | Polytype
  deriving (Show, Eq)

data CType :: TypeCategory -> * where
  TyArrow :: CType a -> CType a -> CType a
  TyUnit :: CType a
  TyVar :: TyName -> CType a
  TyExists :: TyName -> CType a
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

data CtxElem
  = CtxForall TyName
  | CtxVar TmName (CType 'Polytype)
  | CtxExist TyName
  | CtxExistSolved TyName (CType 'Monotype)
  | CtxMarker TyName
  deriving (Show, Eq)

type Context = [CtxElem]

lookupTypeOfVar :: Context -> TmName -> Maybe (CType 'Polytype)
lookupTypeOfVar [] _ = Nothing
lookupTypeOfVar (c : cs) n =
  case c of
    (CtxVar vn ty) ->
      if vn == n
        then Just ty
        else lookupTypeOfVar cs n
    _ -> lookupTypeOfVar cs n

data Term a
  = Ann (Term a) (CType a)
  | Var TmName
  | Unit
  | App (Term a) (Term a)
  | Abs (Term a)
  deriving (Show, Eq)

-- zero :: Term
-- zero = TmAbs "f" TyUnit (TmAbs "x" TyUnit (TmVar "x" 0))

zero :: (Term a)
zero = Abs (Abs (Var (TmI 0)))

synthType :: Term 'Polytype -> Maybe (CType 'Polytype)
synthType tm =
  let initState =
        ScopeState
          { termIdx = 0,
            typeIdx = 0,
            freeCount = 0,
            context = []
          }
   in evalState (synthType' tm) initState

-- synthType :: Context -> Term 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
-- synthType = synthType'

synthType' :: Term 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
synthType' (Ann tm ty) =
  do
    chk <- checkType tm ty
    return $ if chk then Just ty else Nothing
synthType' (Var n) = do
  ctx <- gets context
  return $ lookupTypeOfVar ctx n
synthType' Unit = return $ Just TyUnit
synthType' (App ts tc) =
  do
    mt <- synthType' ts
    case mt of
      Just t -> synthApplyType tc t
      Nothing -> return Nothing
synthType' (Abs tm) =
  do
    ctx <- gets context
    freeCnt <- gets freeCount
    let alpha = TyN (freeCnt + 1)
    let beta = TyN (freeCnt + 2)
    let ctx' = CtxExist beta : CtxExist alpha : CtxMarker alpha : ctx

    modify (\s -> s {freeCount = freeCnt + 2, context = ctx'})
    chk <- checkType tm (TyExists beta)
    modify (\s -> s {freeCount = freeCnt, context = ctx})

    if chk
      then return $ Just (TyArrow (TyExists alpha) (TyExists beta))
      else return Nothing

synthApplyType :: Term 'Polytype -> CType 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
synthApplyType = undefined

-- todo forall/exists
checkType :: Term 'Polytype -> CType 'Polytype -> ScopeGen Bool
checkType (Abs tm) (TyArrow ty1 ty2) =
  do
    tmIdx <- gets termIdx
    ctx <- gets context
    let ctx' = CtxVar (TmI tmIdx) ty1 : ctx
    modify (\s -> s {termIdx = tmIdx + 1, context = ctx'})
    ret <- checkType (subst (TmI 0) (Var (TmI tmIdx)) tm) ty2
    modify (\s -> s {termIdx = tmIdx, context = ctx})
    return ret
checkType tm (TyForall ty) =
  do
    tyIdx <- gets typeIdx
    ctx <- gets context
    let ctx' = CtxForall (TyI tyIdx) : ctx
    modify (\s -> s {typeIdx = tyIdx + 1, context = ctx'})
    ret <- checkType tm (typeSubst (TyI 0) (TyVar (TyI tyIdx)) ty)
    modify (\s -> s {typeIdx = tyIdx, context = ctx})
    return ret
checkType Unit TyUnit = return True
checkType tm ty =
  do
    t <- synthType' tm
    return $ case t of
      Just infTy -> infTy == ty
      Nothing -> False

subst :: TmName -> Term a -> Term a -> Term a
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
typeSubst i ty' (TyExists n) = undefined
typeSubst i ty' (TyForall ty1) = undefined
