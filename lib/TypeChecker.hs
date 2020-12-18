{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module TypeChecker where

import Control.Applicative (Applicative (liftA2))

newtype TmIdx = TmIdx Int
  deriving (Show, Eq, Num)

newtype TyIdx = TyIdx Int
  deriving (Show, Eq, Num)

data Indices = Indices TmIdx TyIdx
  deriving (Show, Eq)

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

synthType :: Context -> Term 'Polytype -> Maybe (CType 'Polytype)
synthType = synthType' (Indices 0 0)

synthType' :: Indices -> Context -> Term 'Polytype -> Maybe (CType 'Polytype)
synthType' i ctx (Ann tm ty) =
  if checkType i ctx tm ty
    then Just ty
    else Nothing
synthType' _ ctx (Var n) = lookupTypeOfVar ctx n
synthType' _ _ Unit = Just TyUnit
synthType' i ctx (App ts tc) =
  case synthType' i ctx ts of
    Just t -> synthApplyType i ctx tc t
    _ -> Nothing

-- synthType' (Indices tmIdx tyIdx) ctx (Abs tm) =
--   let marker = CtxMarker (tyIdx + 1)
--       alpha = CtxExist (tyIdx + 1)
--       beta = CtxExist (tyIdx + 2)
--       x = CtxVar (tmIdx + 1) ()
--    in undefined

synthApplyType :: Indices -> Context -> Term 'Polytype -> CType 'Polytype -> Maybe (CType 'Polytype)
synthApplyType = undefined

-- todo forall/exists
checkType :: Indices -> Context -> Term 'Polytype -> CType 'Polytype -> Bool
checkType (Indices tmIdx tyIdx) ctx (Abs tm) (TyArrow ty1 ty2) =
  checkType (Indices (tmIdx + 1) tyIdx) (CtxVar tmIdx ty1 : ctx) (subst 0 (Var tmIdx) tm) ty2
checkType (Indices tmIdx tyIdx) ctx tm (TyForall ty) =
  checkType (Indices tmIdx (tyIdx + 1)) (CtxForall tyIdx : ctx) tm (typeSubst 0 (TyVar tyIdx) ty)
checkType _ _ Unit TyUnit = True
checkType i ctx tm ty = case synthType' i ctx tm of
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
