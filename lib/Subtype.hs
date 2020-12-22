{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Subtype where

import Control.Monad.State
import qualified Data.Set as S
import Types

solve :: FreeName -> CType a -> ScopeGen (Either String ())
solve alpha a = case ctypeToMono a of
  Just t -> do
    fc <- gets freeCount
    ctx <- gets context
    let (l, _) = breakMarker (CtxExist alpha) ctx
    let wf = typeWF l fc a
    if wf
      then do
        let ctx' = replaceCtxExistWith ctx (CtxExist alpha) [CtxExistSolved alpha t]
        modify (\s -> s {context = ctx'})
        succeed
      else failWith $ "Type: " ++ show a ++ " is not well-formed"
  Nothing -> failWith $ "Type: " ++ show a ++ " is not a monotype"

freeTyVars :: CType a -> S.Set FreeName
freeTyVars ty = case ty of
  TyUnit -> S.empty
  TyVar (TyN n) -> S.singleton n
  TyVar (TyI _) -> S.empty
  TyForall t -> freeTyVars t
  TyExists n -> S.singleton n
  TyArrow ty1 ty2 -> S.union (freeTyVars ty1) (freeTyVars ty2)

lookupSolution :: Context -> FreeName -> Maybe (CType 'Monotype)
lookupSolution [] _ = Nothing
lookupSolution (c : cs) n =
  case c of
    (CtxExistSolved vn ty) ->
      if vn == n
        then Just ty
        else lookupSolution cs n
    _ -> lookupSolution cs n

-- TODO: Remove from state monad
comesBefore :: FreeName -> FreeName -> ScopeGen Bool
comesBefore alpha beta = do
  ctx <- gets context
  dropMarker (CtxExist beta)
  ctx' <- gets context
  let ret = alpha `elem` existentials ctx'
  modify (\s -> s {context = ctx})
  return ret

apply :: Context -> CType 'Polytype -> CType 'Polytype
apply ctx ty = case ty of
  TyUnit -> TyUnit
  TyVar n -> TyVar n
  TyForall t -> TyForall $ apply ctx t
  tye@(TyExists n) ->
    case lookupSolution ctx n of
      Just t -> apply ctx (ctypeToPoly t)
      Nothing -> tye
  TyArrow ty1 ty2 -> TyArrow (apply ctx ty1) (apply ctx ty2)

existentials :: Context -> [FreeName]
existentials = go
  where
    go [] = []
    go ((CtxExist n) : xs) = n : go xs
    go ((CtxExistSolved n _) : xs) = n : go xs
    go (_ : xs) = go xs

unsolvedExi :: Context -> [FreeName]
unsolvedExi = go
  where
    go [] = []
    go ((CtxExist n) : xs) = n : go xs
    go (_ : xs) = go xs

foralls :: Context -> [FreeName]
foralls = go
  where
    go [] = []
    go ((CtxForall n) : xs) = n : go xs
    go (_ : xs) = go xs

vars :: Context -> [FreeName]
vars = go
  where
    go [] = []
    go ((CtxVar n _) : xs) = n : go xs
    go (_ : xs) = go xs

markers :: Context -> [FreeName]
markers = go
  where
    go [] = []
    go ((CtxMarker n) : xs) = n : go xs
    go (_ : xs) = go xs

ctxWF :: Context -> FreeName -> Bool
-- Empty-Ctx
ctxWF [] _ = True
ctxWF (c : cs) fc =
  ctxWF cs fc && case c of
    -- U-Var-Ctx
    CtxForall n -> n `notElem` foralls cs
    -- Var-Ctx
    CtxVar n ty -> (n `notElem` vars cs) && typeWF cs fc ty
    -- E-Var-Ctx
    CtxExist n -> n `notElem` existentials cs
    -- Solved-E-Var-Ctx
    CtxExistSolved n ty -> (n `notElem` existentials cs) && typeWF cs fc ty
    -- Marker-Ctx
    CtxMarker n -> n `notElem` markers cs && n `notElem` existentials cs

typeWF :: Context -> FreeName -> CType a -> Bool
typeWF ctx fc ty = case ty of
  -- U-Var-WF
  TyVar (TyN n) -> n `elem` foralls ctx
  TyVar (TyI _) -> False
  -- Unit-WF
  TyUnit -> True
  -- Arrow-WF
  TyArrow a b -> typeWF ctx fc a && typeWF ctx fc b
  -- Forall-WF
  TyForall a -> typeWF (CtxForall fc : ctx) (fc + 1) (typeSubst (TyI 0) (TyVar (TyN fc)) a)
  -- E-Var-WF and Solved-E-Var-WF
  TyExists n -> n `elem` existentials ctx

checkCtxWF :: ScopeGen Bool
checkCtxWF = do
  fc <- gets freeCount
  ctx <- gets context
  return $ ctxWF ctx fc

checkTypeWF :: CType 'Polytype -> ScopeGen (Either String ())
checkTypeWF ty = do
  fc <- gets freeCount
  ctx <- gets context
  if typeWF ctx fc ty
    then succeed
    else failWith $ "Type: " ++ show ty ++ " is not well-formed"

subtype :: CType a -> CType a -> ScopeGen (Either String ())
subtype ty1 ty2 = do
  ctx <- gets context
  case (ty1, ty2) of
    -- <:Var
    (TyVar n, TyVar n')
      | n == n' -> succeed
    -- <:Unit
    (TyUnit, TyUnit) -> succeed
    -- <:ExVar
    (TyExists n, TyExists n')
      | n == n' && n `elem` existentials ctx -> succeed
    -- <:→
    (TyArrow a1 a2, TyArrow b1 b2) -> do
      st1 <- subtype b1 a1
      ctx' <- gets context
      st2 <- subtype (apply ctx' (ctypeToPoly a2)) (apply ctx' (ctypeToPoly b2))
      return (return st1 st2)
    -- <:∀R
    (a, TyForall ty) -> do
      (alpha, m) <- addNewToCtx CtxForall
      st <- subtype a (typeSubst (TyI 0) (TyVar (TyN alpha)) ty)
      dropMarker m
      return st
    -- <:∀L
    (TyForall ty, a) -> do
      (alpha, e) <- newFree CtxExist
      let marker = CtxMarker alpha
      appendToCtx [marker, e]
      st <- subtype (typeSubst (TyI 0) (TyExists alpha) ty) a
      dropMarker marker
      return st
    -- <:InstantiateL
    (TyExists n, a)
      | (n `elem` existentials ctx)
          && n `notElem` freeTyVars a ->
        instantiateL n (ctypeToPoly a)
    -- <:InstantiateR
    (a, TyExists n)
      | (n `elem` existentials ctx)
          && n `notElem` freeTyVars a ->
        instantiateR (ctypeToPoly a) n
    _ -> failWith "Couldn't match any case in the function: subtype"

instantiateL :: FreeName -> CType 'Polytype -> ScopeGen (Either String ())
instantiateL alpha a = do
  solvedA <- solve alpha a
  case solvedA of
    -- Inst-L-Solve
    Right _ -> succeed
    Left _ ->
      case a of
        -- Inst-L-Reach
        TyExists beta -> solve beta (TyExists alpha)
        -- Inst-L-Arr
        TyArrow ty1 ty2 -> do
          (alpha1, e1) <- newFree CtxExist
          (alpha2, e2) <- newFree CtxExist
          let ctxToAdd =
                [ e2,
                  e1,
                  CtxExistSolved alpha (TyArrow (TyExists alpha1) (TyExists alpha2))
                ]
          ctx <- gets context
          let ctx' = replaceCtxExistWith ctx (CtxExist alpha) ctxToAdd
          modify (\s -> s {context = ctx'})
          ir <- instantiateR ty1 alpha1
          ctx'' <- gets context
          il <- instantiateL alpha2 (apply ctx'' ty2)
          return (return ir il)
        -- Inst-L-All-R
        TyForall b -> do
          (beta, m) <- addNewToCtx CtxForall
          ret <- instantiateL alpha (typeSubst (TyI 0) (TyVar (TyN beta)) b)
          dropMarker m
          return ret
        _ -> failWith "Couldn't match any case in the function: instantiateL"

instantiateR :: CType 'Polytype -> FreeName -> ScopeGen (Either String ())
instantiateR a alpha = do
  solvedA <- solve alpha a
  case solvedA of
    -- Inst-R-Solve
    Right _ -> succeed
    Left _ ->
      case a of
        -- Inst-R-Reach
        TyExists beta -> solve beta (TyExists alpha)
        -- Inst-R-Arr
        TyArrow ty1 ty2 -> do
          (alpha1, e1) <- newFree CtxExist
          (alpha2, e2) <- newFree CtxExist
          let ctxToAdd =
                [ e2,
                  e1,
                  CtxExistSolved alpha (TyArrow (TyExists alpha1) (TyExists alpha2))
                ]

          ctx <- gets context
          let ctx' = replaceCtxExistWith ctx (CtxExist alpha) ctxToAdd
          modify (\s -> s {context = ctx'})
          il <- instantiateL alpha1 ty1
          ctx'' <- gets context
          ir <- instantiateR (apply ctx'' ty2) alpha2
          return (return il ir)
        -- Inst-R-All-L
        TyForall b -> do
          (beta, e) <- newFree CtxExist
          let marker = CtxMarker beta
          appendToCtx [marker, e]
          ret <- instantiateR (typeSubst (TyI 0) (TyExists beta) b) alpha
          dropMarker marker
          return ret
        _ -> failWith "Couldn't match any case in the function: instantiateR"
