{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module TypeChecker where

import Control.Monad.State
import Subtype (apply, checkTypeWF, subtype, unsolvedExi)
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
          { freeCount = 0,
            context = []
          }
   in evalState (synthType' tm) initState

synthType' :: Term -> ScopeGen (Maybe (CType 'Polytype))
-- Anno
synthType' (Ann tm ty) =
  do
    tw <- checkTypeWF ty
    if tw
      then do
        chk <- checkType tm ty
        return $ if chk then Just ty else Nothing
      else return Nothing
-- Var
synthType' (Var (TmN n)) = do
  ctx <- gets context
  return $ lookupTypeOfVar ctx n
-- Var (not applicable)
synthType' (Var (TmI _)) = return Nothing
-- 1I-synth
synthType' Unit = return $ Just TyUnit
-- →E
synthType' (App ts tc) =
  do
    mt <- synthType' ts
    ctx <- gets context
    case mt of
      Just t -> do
        let a = apply ctx t
        synthApplyType tc a
      Nothing -> return Nothing

-- →I-Synth (Damas-Milner)
synthType' (Abs tm) = do
  (alpha, e1) <- newFree CtxExist
  (beta, e2) <- newFree CtxExist
  (x, e3) <- newFree $ flip CtxVar (TyExists alpha)
  let marker = CtxMarker alpha
  appendToCtx [marker, e1, e2, e3]
  chk <- checkType (subst (TmI 0) (Var (TmN x)) tm) (TyExists beta)

  if chk
    then do
      ctx <- gets context
      let (delta, delta') = breakMarker marker ctx
      let tau = apply delta' (TyArrow (TyExists alpha) (TyExists beta))
      let unsolved = unsolvedExi delta'
      let t = foldr addForall tau unsolved
      modify (\s -> s {context = delta})
      return $ Just t
    else return Nothing

-- →I-Synth (Original rule)
-- synthType' (Abs tm) =
--   do
--     (alpha, e1) <- newFree CtxExist
--     (beta, e2) <- newFree CtxExist
--     (x, e3) <- newFree $ flip CtxVar (TyExists alpha)
--     appendToCtx [e1, e2, e3]

--     chk <- checkType (subst (TmI 0) (Var (TmN x)) tm) (TyExists beta)
--     dropMarker e3

--     if chk
--       then return $ Just (TyArrow (TyExists alpha) (TyExists beta))
--       else return Nothing

synthApplyType :: Term -> CType 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
-- ∀App
synthApplyType tm (TyForall ty) =
  do
    (alpha', _) <- addNewToCtx CtxExist
    synthApplyType tm (typeSubst (TyI 0) (TyExists alpha') ty)
-- âApp
synthApplyType tm (TyExists ty) =
  do
    (beta, e1) <- newFree CtxExist
    (alpha, e2) <- newFree CtxExist
    let solved = CtxExistSolved ty (TyArrow (TyExists alpha) (TyExists beta))
    let ctxToAdd = [e1, e2, solved]

    ctx <- gets context
    let ctx' = replaceCtxExistWith ctx (CtxExist ty) ctxToAdd
    modify (\s -> s {context = ctx'})

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
    (x, m) <- addNewToCtx $ flip CtxVar ty1
    ret <- checkType (subst (TmI 0) (Var (TmN x)) tm) ty2
    dropMarker m
    return ret
-- ∀I
checkType tm (TyForall ty) =
  do
    (alpha, m) <- addNewToCtx CtxForall
    ret <- checkType tm (typeSubst (TyI 0) (TyVar (TyN alpha)) ty)
    dropMarker m
    return ret
-- 1I
checkType Unit TyUnit = return True
-- Sub
checkType tm ty =
  do
    mt <- synthType' tm
    ctx <- gets context
    case mt of
      Just t -> subtype (apply ctx t) (apply ctx ty)
      Nothing -> return False