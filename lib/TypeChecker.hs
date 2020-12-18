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

data Indices = Indices TmIdx TyIdx
  deriving (Show, Eq)

-- The state of indices and free names generate
data ScopeState = ScopeState
  { termIdx :: TmIdx,
    typeIdx :: TyIdx,
    freeCount :: FreeName
  }
  deriving (Show, Eq)

-- Type alias for the State monad
type ScopeGen a = State ScopeState a

data TypeCategory = Monotype | Polytype
  deriving (Show, Eq)

data CType :: TypeCategory -> * where
  TyArrow :: CType a -> CType a -> CType a
  TyUnit :: CType a
  TyVar :: TyIdx -> CType a
  TyExists :: TyIdx -> CType a
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
  = CtxForall TyIdx
  | CtxVar TmIdx (CType 'Polytype)
  | CtxExist TyIdx
  | CtxExistSolved TyIdx (CType 'Monotype)
  | CtxMarker TyIdx

type Context = [CtxElem]

lookupTypeOfVar :: Context -> TmIdx -> Maybe (CType 'Polytype)
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
  | Var TmIdx
  | Unit
  | App (Term a) (Term a)
  | Abs (Term a)
  deriving (Show, Eq)

-- zero :: Term
-- zero = TmAbs "f" TyUnit (TmAbs "x" TyUnit (TmVar "x" 0))

zero :: (Term a)
zero = Abs (Abs (Var 0))

synthType :: Term 'Polytype -> Maybe (CType 'Polytype)
synthType tm =
  let initState =
        ScopeState
          { termIdx = 0,
            typeIdx = 0,
            freeCount = 0
          }
   in evalState (synthType' [] tm) initState

-- synthType :: Context -> Term 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
-- synthType = synthType'

synthType' :: Context -> Term 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
synthType' ctx (Ann tm ty) =
  do
    chk <- checkType ctx tm ty
    return $ if chk then Just ty else Nothing
synthType' ctx (Var n) = return $ lookupTypeOfVar ctx n
synthType' _ Unit = return $ Just TyUnit
synthType' ctx (App ts tc) =
  do
    mt <- synthType' ctx ts
    case mt of
      Just t -> synthApplyType ctx tc t
      Nothing -> return Nothing

-- -- TODO: FINISH THIS
-- synthType' ctx (Abs tm) =
--   do
--     -- state <- get
--     freeCnt <- gets freeCount
--     let alpha = freeCnt + 1
--     let beta = freeCnt + 2
--     -- let x = CtxVar (freeCnt + 3)
--     let ctx' = CtxExist beta : CtxExist alpha : CtxMarker alpha : ctx

--     modify {freeCount = freeCnt + 2}
--     chk <- checkType ctx' tm (TyExists beta)
--     modify {freeCount = freeCnt}

--     if chk
--       then return (TyArrow (TyExists alpha) (TyExists beta))
--       else return Nothing

--     return Nothing
synthType' _ _ = return Nothing

-- TODO: We can refactor the Context into the state
synthApplyType :: Context -> Term 'Polytype -> CType 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
synthApplyType = undefined

-- todo forall/exists
checkType :: Context -> Term 'Polytype -> CType 'Polytype -> ScopeGen Bool
checkType ctx (Abs tm) (TyArrow ty1 ty2) =
  do
    tmIdx <- gets termIdx
    modify (\s -> s {termIdx = tmIdx + 1})
    ret <- checkType (CtxVar tmIdx ty1 : ctx) (subst 0 (Var tmIdx) tm) ty2
    modify (\s -> s {termIdx = tmIdx})
    return ret
checkType ctx tm (TyForall ty) =
  do
    tyIdx <- gets typeIdx
    modify (\s -> s {typeIdx = tyIdx + 1})
    ret <- checkType (CtxForall tyIdx : ctx) tm (typeSubst 0 (TyVar tyIdx) ty)
    modify (\s -> s {typeIdx = tyIdx})
    return ret
checkType _ Unit TyUnit = return True
checkType ctx tm ty =
  do
    t <- synthType' ctx tm
    return $ case t of
      Just infTy -> infTy == ty
      Nothing -> False

subst :: TmIdx -> Term a -> Term a -> Term a
subst i tm1 (Ann tm2 ty) = Ann (subst i tm1 tm2) ty
subst i tm1 (Abs tm2) = Abs (subst (i + 1) tm1 tm2)
subst i tm (Var j) = if i == j then tm else Var j
subst i tm (App tm1 tm2) = App (subst i tm tm1) (subst i tm tm2)
subst _ _ Unit = Unit

typeSubst :: TyIdx -> CType a -> CType a -> CType a
typeSubst i ty' (TyArrow ty1 ty2) = TyArrow (typeSubst i ty' ty1) (typeSubst i ty' ty2)
typeSubst _ _ TyUnit = TyUnit
typeSubst i ty' (TyVar n) =
  if i == n
    then ty'
    else TyVar n
typeSubst i ty' (TyExists n) = undefined
typeSubst i ty' (TyForall ty1) = undefined
