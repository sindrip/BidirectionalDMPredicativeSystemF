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

synthType :: Term -> Either String (CType 'Polytype)
synthType tm =
  let initState =
        ScopeState
          { freeCount = 0,
            context = []
          }
   in evalState (synthType' tm) initState

synthType' :: Term -> ScopeGen (Either String (CType 'Polytype))
-- Anno
synthType' (Ann tm ty) =
  do
    tw <- checkTypeWF ty
    case tw of
      Left e -> failWith e
      Right _ -> do
        chk <- checkType tm ty
        case chk of
          Left e -> failWith e
          Right _ -> succeedWith ty
-- Var
synthType' (Var (TmN n)) = do
  ctx <- gets context
  case lookupTypeOfVar ctx n of
    Nothing -> failWith "Cannot find variable in context"
    Just ty -> succeedWith ty

-- case lookupTypeOfVar ctx n of

-- Var (not applicable)
synthType' (Var (TmI _)) = failWith "Unscoped bound variable encountered"
-- 1I-synth
synthType' Unit = succeedWith TyUnit
-- →E (Damas-Milner)
--
-- This rule change is not mentioned in the paper
-- Without this change, we cannot synthesize simple types such as
-- succ (Zero)
--
-- With it, we can synthesize types for church numerals with succ
--
synthType' (App ts tc) =
  do
    mt <- synthType' ts
    case mt of
      Left e -> failWith e
      Right t -> do
        ctx <- gets context
        let a = apply ctx t

        (_, marker) <- newFree CtxMarker
        appendToCtx [marker]

        sat <- synthApplyType tc a

        case sat of
          Left e -> failWith e
          Right sty -> do
            ctx' <- gets context
            let (delta, delta') = breakMarker marker ctx'
            let tau = apply delta' sty
            let unsolved = unsolvedExi delta'
            let rt = foldr addForall tau unsolved
            modify (\s -> s {context = delta})
            succeedWith rt
-- -- →E (Old rule)
-- synthType' (App ts tc) =
--   do
--     mt <- synthType' ts
--     case mt of
--       Left e -> failWith e
--       Right t -> do
--         ctx <- gets context
--         let a = apply ctx t
--         synthApplyType tc a
-- →I-Synth (Damas-Milner)
synthType' (Abs tm) = do
  (alpha, e1) <- newFree CtxExist
  (beta, e2) <- newFree CtxExist
  (x, e3) <- newFree $ flip CtxVar (TyExists alpha)
  let marker = CtxMarker alpha
  appendToCtx [marker, e1, e2, e3]
  chk <- checkType (subst (TmI 0) (Var (TmN x)) tm) (TyExists beta)

  case chk of
    Left e -> failWith e
    Right _ -> do
      ctx <- gets context
      let (delta, delta') = breakMarker marker ctx
      let tau = apply delta' (TyArrow (TyExists alpha) (TyExists beta))
      let unsolved = unsolvedExi delta'
      let t = foldr addForall tau unsolved
      modify (\s -> s {context = delta})
      succeedWith t

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

synthApplyType :: Term -> CType 'Polytype -> ScopeGen (Either String (CType 'Polytype))
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
    case chk of
      Left e -> failWith e
      Right _ -> succeedWith (TyExists beta)
-- →App
synthApplyType tm (TyArrow ty1 ty2) =
  do
    chk <- checkType tm ty1
    case chk of
      Left e -> failWith e
      Right _ -> succeedWith ty2
synthApplyType _ _ = failWith "Couldn't match any case in the function: synthApplyType"

checkType :: Term -> CType 'Polytype -> ScopeGen (Either String ())
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
checkType Unit TyUnit = succeed
-- Sub
checkType tm ty =
  do
    mt <- synthType' tm
    ctx <- gets context
    case mt of
      Left e -> failWith e
      Right t -> subtype (apply ctx t) (apply ctx ty)

ppTy :: CType a -> IO ()
ppTy = putStrLn . go 0
  where
    go :: Int -> CType a -> String
    go i (TyArrow ty1 ty2) = "(" ++ go i ty1 ++ " → " ++ go i ty2 ++ ")"
    go _ TyUnit = "Unit"
    go _ (TyVar (TyN (FreeName n))) = show n
    go _ (TyVar (TyI (TyIdx j))) = show j ++ "'"
    go _ (TyExists (FreeName n)) = "∃" ++ show n
    go i (TyForall ty) = "∀" ++ show i ++ "': " ++ go (i + 1) ty

infer :: Term -> IO ()
infer tm =
  let mty = synthType tm
   in case mty of
        Left e -> putStrLn e
        Right ty -> ppTy ty
