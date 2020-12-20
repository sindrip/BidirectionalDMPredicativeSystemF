{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Subtype where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.State
import qualified Data.Set as S
import Types

solve :: FreeName -> CType a -> ScopeGen Bool
solve alpha a = case ctypeToMono a of
  Just t -> do
    ctx <- gets context
    let ctxToAdd = [CtxExistSolved alpha t]
    let ctx' = replaceCtxExistWith ctx (CtxExist alpha) ctxToAdd
    modify (\s -> s {context = ctx'})
    return True
  Nothing -> return False

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

comesBefore :: FreeName -> FreeName -> ScopeGen Bool
comesBefore alpha beta = do
  ctx <- gets context
  dropMarker (CtxExist beta)
  ctx' <- gets context
  let ret = alpha `elem` existentials ctx'
  modify (\s -> s {context = ctx})
  return ret

apply :: CType 'Polytype -> ScopeGen (CType 'Polytype)
apply ty = do
  ctx <- gets context
  case ty of
    TyUnit -> return TyUnit
    TyVar n -> return $ TyVar n
    TyForall t -> TyForall <$> apply t
    tye@(TyExists n) ->
      case lookupSolution ctx n of
        Just t -> apply (ctypeToPoly t)
        Nothing -> return tye
    TyArrow ty1 ty2 -> liftA2 TyArrow (apply ty1) (apply ty2)

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

ctxWF :: ScopeGen Bool
ctxWF = do
  ctx <- gets context
  go ctx
  where
    go :: Context -> ScopeGen Bool
    go [] = return True
    go (c : cs) = case c of
      CtxForall n -> return $ n `notElem` foralls cs
      CtxVar n ty -> do
        modify (\s -> s {context = cs})
        chk <- (&&) (n `notElem` vars cs) <$> typeWF ty
        modify (\s -> s {context = cs})
        return chk
      CtxExist n -> return $ n `notElem` existentials cs
      CtxExistSolved n ty -> do
        modify (\s -> s {context = cs})
        chk <- (&&) (n `notElem` existentials cs) <$> typeWF ty
        modify (\s -> s {context = cs})
        return chk
      CtxMarker n ->
        return $ n `notElem` markers cs && n `notElem` existentials cs

typeWF :: CType a -> ScopeGen Bool
typeWF ty = do
  ctx <- gets context
  case ty of
    TyVar (TyN n) -> return $ n `elem` foralls ctx
    TyVar (TyI _) -> return False
    TyUnit -> return True
    TyArrow a b -> liftA2 (&&) (typeWF a) (typeWF b)
    TyForall a -> do
      freeCnt <- gets freeCount
      let alpha = freeCnt
      let ctx' = CtxForall alpha : ctx

      modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
      chk <- typeWF (typeSubst (TyI 0) (TyExists alpha) a)
      modify (\s -> s {freeCount = freeCnt, context = ctx})
      return chk
    TyExists n -> return $ n `elem` existentials ctx

checkCtxWF :: ScopeGen Bool
checkCtxWF = do ctxWF

checkTypeWF :: CType 'Polytype -> ScopeGen Bool
checkTypeWF = do typeWF

subtype :: CType a -> CType a -> ScopeGen Bool
subtype ty1 ty2 = do
  ctx <- gets context
  wf1 <- checkTypeWF (ctypeToPoly ty1)
  wf2 <- checkTypeWF (ctypeToPoly ty2)
  st <- case (ty1, ty2) of
    -- <:Var
    (TyVar n, TyVar n') -> return $ n == n'
    -- <:Unit
    (TyUnit, TyUnit) -> return True
    -- <:ExVar
    (TyExists n, TyExists n') -> return $ n == n' && n `elem` existentials ctx
    -- <:→
    (TyArrow a1 a2, TyArrow b1 b2) -> do
      ctx' <- gets context
      st1 <- subtype b1 a1
      st2 <- subtype <$> apply (ctypeToPoly a2) <*> apply (ctypeToPoly b2)
      modify (\s -> s {context = ctx'})
      (&&) st1 <$> st2
    -- <:∀R
    (a, TyForall ty) -> do
      ctx' <- gets context
      freeCnt <- gets freeCount
      let alpha = freeCnt
      let ctx'' = CtxForall alpha : ctx'
      modify (\s -> s {context = ctx''})
      st <- subtype a (typeSubst (TyI 0) (TyVar (TyN alpha)) ty)
      dropMarker (CtxForall alpha)
      return st
    -- <:∀L
    (TyForall ty, a) -> do
      ctx' <- gets context
      freeCnt <- gets freeCount
      let alpha = freeCnt
      let ctx'' = CtxExist alpha : CtxMarker alpha : ctx'
      modify (\s -> s {context = ctx''})
      st <- subtype (typeSubst (TyI 0) (TyVar (TyN alpha)) ty) a
      dropMarker (CtxMarker alpha)
      return st
    -- <:InstantiateL
    (TyExists n, a) -> do
      ctx' <- gets context
      (&&)
        ( (n `elem` existentials ctx')
            && n `notElem` freeTyVars a
        )
        <$> instantiateL n (ctypeToPoly a)
    -- <:InstantiateR
    (a, TyExists n) -> do
      ctx' <- gets context
      (&&)
        ( (n `elem` existentials ctx')
            && n `notElem` freeTyVars a
        )
        <$> instantiateR (ctypeToPoly a) n
    _ -> return False
  return $ wf1 && wf2 && st

instantiateL :: FreeName -> CType 'Polytype -> ScopeGen Bool
instantiateL alpha a = do
  wf1 <- checkTypeWF (ctypeToPoly a)
  wf2 <- checkTypeWF (ctypeToPoly (TyExists alpha))
  solvedA <- solve alpha a
  if solvedA
    then return $ wf1 && wf2
    else case a of
      TyExists beta -> do
        aBefore <- comesBefore alpha beta
        if aBefore
          then solve beta (TyExists alpha)
          else solve alpha (TyExists beta)
      TyArrow a1 a2 -> do
        ctx <- gets context
        freeCnt <- gets freeCount
        let alpha1 = freeCnt
        let alpha2 = freeCnt + 1
        let ctxToAdd =
              [ CtxExistSolved alpha (TyArrow (TyExists alpha1) (TyExists alpha2)),
                CtxExist alpha1,
                CtxExist alpha2
              ]
        let ctx' = replaceCtxExistWith ctx (CtxExist alpha) ctxToAdd
        modify (\s -> s {context = ctx', freeCount = freeCnt + 2})
        liftA2 (&&) (instantiateR a1 alpha1) (apply a2 >>= instantiateL alpha2)
      TyForall b -> do
        ctx <- gets context
        freeCnt <- gets freeCount
        let beta' = freeCnt
        let ctx' = CtxForall beta' : ctx

        modify (\s -> s {context = ctx', freeCount = freeCnt + 1})
        ret <- instantiateL alpha (typeSubst (TyI 0) (TyForall (TyVar (TyN beta'))) b)
        dropMarker (CtxForall beta')

        return ret
      _ -> return False

instantiateR :: CType 'Polytype -> FreeName -> ScopeGen Bool
instantiateR a alpha = do
  wf1 <- checkTypeWF (ctypeToPoly a)
  wf2 <- checkTypeWF (ctypeToPoly (TyExists alpha))
  solvedA <- solve alpha a
  if solvedA
    then return $ wf1 && wf2
    else case a of
      TyExists beta -> do
        aBefore <- comesBefore alpha beta
        if aBefore
          then solve beta (TyExists alpha)
          else solve alpha (TyExists beta)
      TyArrow a1 a2 -> do
        ctx <- gets context
        freeCnt <- gets freeCount
        let alpha1 = freeCnt
        let alpha2 = freeCnt + 1
        let ctxToAdd =
              [ CtxExistSolved alpha (TyArrow (TyExists alpha1) (TyExists alpha2)),
                CtxExist alpha1,
                CtxExist alpha2
              ]
        let ctx' = replaceCtxExistWith ctx (CtxExist alpha) ctxToAdd
        modify (\s -> s {context = ctx', freeCount = freeCnt + 2})
        liftA2 (&&) (instantiateL alpha1 a1) (apply a2 >>= flip instantiateR alpha2)
      TyForall b -> do
        ctx <- gets context
        freeCnt <- gets freeCount
        let beta' = freeCnt
        let ctx' = CtxExist beta' : CtxMarker beta' : ctx

        modify (\s -> s {context = ctx', freeCount = freeCnt + 1})
        ret <- instantiateL alpha (typeSubst (TyI 0) (TyExists beta') b)
        dropMarker (CtxMarker beta')

        return ret
      _ -> return False