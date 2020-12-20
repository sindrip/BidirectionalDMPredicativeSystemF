{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module TypeChecker where

import Control.Monad.State
import Subtype (subtype)
import Types

lookupTypeOfVar :: Context -> FreeName -> Maybe (CType 'Polytype)
lookupTypeOfVar [] _ = Nothing
lookupTypeOfVar (c : cs) n =
  case c of
    (CtxVar vn ty) ->
      if vn == n
        then Just ty
        else lookupTypeOfVar cs n
    _ -> lookupTypeOfVar cs n

synthType :: Term -> Maybe (CType 'Polytype)
synthType tm =
  let initState =
        ScopeState
          { termIdx = 0,
            typeIdx = 0,
            freeCount = 0,
            context = []
          }
   in evalState (synthType' tm) initState

synthType' :: Term -> ScopeGen (Maybe (CType 'Polytype))
-- Anno
synthType' (Ann tm ty) =
  do
    chk <- checkType tm ty
    return $ if chk then Just ty else Nothing
-- Var
synthType' (Var (TmN n)) = do
  ctx <- gets context
  return $ lookupTypeOfVar ctx n
-- Var (not applicable)
synthType' (Var (TmI _)) = return Nothing
-- 1I-synth
synthType' Unit = return $ Just TyUnit
-- →I-Synth
synthType' (App ts tc) =
  do
    mt <- synthType' ts
    case mt of
      Just t -> synthApplyType tc t
      Nothing -> return Nothing
-- →E
synthType' (Abs tm) =
  do
    ctx <- gets context
    freeCnt <- gets freeCount
    let alpha = freeCnt
    let beta = freeCnt + 1
    let ctx' = CtxExist beta : CtxExist alpha : CtxMarker alpha : ctx

    modify (\s -> s {freeCount = freeCnt + 2, context = ctx'})
    chk <- checkType tm (TyExists beta)
    modify (\s -> s {freeCount = freeCnt, context = ctx})

    if chk
      then return $ Just (TyArrow (TyExists alpha) (TyExists beta))
      else return Nothing

synthApplyType :: Term -> CType 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
-- ∀App
synthApplyType tm (TyForall ty) =
  do
    ctx <- gets context
    freeCnt <- gets freeCount
    let alpha = freeCnt
    let ctx' = CtxExist alpha : ctx

    modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
    t <- synthApplyType tm (typeSubst (TyI 0) (TyExists alpha) ty)
    modify (\s -> s {freeCount = freeCnt, context = ctx})

    return t
-- âApp
synthApplyType tm (TyExists ty) =
  do
    ctx <- gets context
    freeCnt <- gets freeCount
    let alpha = freeCnt
    let beta = freeCnt + 1
    let ctxToAdd = [CtxExistSolved ty (TyArrow (TyExists alpha) (TyExists beta)), CtxExist alpha, CtxExist beta]
    let ctx' = replaceCtxExistWith ctx (CtxExist ty) ctxToAdd

    modify (\s -> s {freeCount = freeCnt + 2, context = ctx'})

    chk <- checkType tm (TyExists alpha)
    return $ if chk then Just $ TyExists beta else Nothing
-- →App
synthApplyType tm (TyArrow ty1 ty2) =
  do
    chk <- checkType tm ty1
    return $ if chk then Just ty2 else Nothing
synthApplyType _ _ = return Nothing

checkType :: Term -> CType 'Polytype -> ScopeGen Bool
-- →I
checkType (Abs tm) (TyArrow ty1 ty2) =
  do
    freeCnt <- gets freeCount
    ctx <- gets context
    let ctx' = CtxVar freeCnt ty1 : ctx
    modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
    ret <- checkType (subst (TmI 0) (Var (TmN freeCnt)) tm) ty2
    dropMarker (CtxVar freeCnt ty1)
    return ret
-- ∀I
checkType tm (TyForall ty) =
  do
    freeCnt <- gets freeCount
    ctx <- gets context
    let ctx' = CtxForall freeCnt : ctx
    modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
    ret <- checkType tm (typeSubst (TyI 0) (TyVar (TyN freeCnt)) ty)
    dropMarker (CtxForall freeCnt)
    return ret
-- 1I
checkType Unit TyUnit = return True
-- Sub
checkType tm ty =
  do
    mt <- synthType' tm
    case mt of
      Just t -> subtype t ty
      Nothing -> return False
