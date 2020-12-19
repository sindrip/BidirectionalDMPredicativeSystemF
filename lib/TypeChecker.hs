{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module TypeChecker where

import Control.Applicative (Applicative (liftA2))
import Control.Monad.State
import qualified Data.Set as S

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

data CtxElem
  = CtxForall FreeName
  | CtxVar FreeName (CType 'Polytype)
  | CtxExist FreeName
  | CtxExistSolved FreeName (CType 'Monotype)
  | CtxMarker FreeName
  deriving (Show, Eq)

type Context = [CtxElem]

existentials :: Context -> [FreeName]
existentials = go
  where
    go [] = []
    go ((CtxExist n) : xs) = n : go xs
    go ((CtxExistSolved n _) : xs) = n : go xs
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

lookupSolution :: Context -> FreeName -> Maybe (CType 'Monotype)
lookupSolution [] _ = Nothing
lookupSolution (c : cs) n =
  case c of
    (CtxExistSolved vn ty) ->
      if vn == n
        then Just ty
        else lookupSolution cs n
    _ -> lookupSolution cs n

lookupTypeOfVar :: Context -> FreeName -> Maybe (CType 'Polytype)
lookupTypeOfVar [] _ = Nothing
lookupTypeOfVar (c : cs) n =
  case c of
    (CtxVar vn ty) ->
      if vn == n
        then Just ty
        else lookupTypeOfVar cs n
    _ -> lookupTypeOfVar cs n

dropMarker :: CtxElem -> ScopeGen ()
dropMarker m = do
  ctx <- gets context
  let ctx' = tail $ dropWhile (/= m) ctx
  modify (\s -> s {context = ctx'})

breakMarker :: CtxElem -> Context -> (Context, Context)
breakMarker m ctx = let (l, _ : r) = break (== m) ctx in (l, r)

replaceCtxExistWith :: Context -> CtxElem -> Context -> Context
replaceCtxExistWith ctx e toInsert =
  let (l, r) = breakMarker e ctx
   in l ++ toInsert ++ r

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

comesBefore :: FreeName -> FreeName -> ScopeGen Bool
comesBefore alpha beta = do
  ctx <- gets context
  dropMarker (CtxExist beta)
  ctx' <- gets context
  let ret = alpha `elem` existentials ctx'
  modify (\s -> s {context = ctx})
  return ret

data Term
  = Ann Term (CType 'Polytype)
  | Var TmName
  | Unit
  | App Term Term
  | Abs Term
  deriving (Show, Eq)

zero :: Term
zero = Abs (Abs (Var (TmI 0)))

eid :: Term
eid = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 0)) (TyVar (TyI 0))))

eidFail :: Term
eidFail = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 0)) TyUnit))

eidFail2 :: Term
eidFail2 = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 1)) (TyVar (TyI 0))))

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

-- synthType :: Context -> Term 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
-- synthType = synthType'

synthType' :: Term -> ScopeGen (Maybe (CType 'Polytype))
synthType' (Ann tm ty) =
  do
    chk <- checkType tm ty
    return $ if chk then Just ty else Nothing
synthType' (Var (TmN n)) = do
  ctx <- gets context
  return $ lookupTypeOfVar ctx n
synthType' (Var (TmI _)) = return Nothing
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
synthApplyType tm (TyArrow ty1 ty2) =
  do
    chk <- checkType tm ty1
    return $ if chk then Just ty2 else Nothing
synthApplyType _ _ = return Nothing

checkType :: Term -> CType 'Polytype -> ScopeGen Bool
checkType (Abs tm) (TyArrow ty1 ty2) =
  do
    freeCnt <- gets freeCount
    ctx <- gets context
    let ctx' = CtxVar freeCnt ty1 : ctx
    modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
    ret <- checkType (subst (TmI 0) (Var (TmN freeCnt)) tm) ty2
    dropMarker (CtxVar freeCnt ty1)
    return ret
checkType tm (TyForall ty) =
  do
    freeCnt <- gets freeCount
    ctx <- gets context
    let ctx' = CtxForall freeCnt : ctx
    modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
    ret <- checkType tm (typeSubst (TyI 0) (TyVar (TyN freeCnt)) ty)
    dropMarker (CtxForall freeCnt)
    return ret
checkType Unit TyUnit = return True
-- Apply context as substitution
checkType tm ty =
  do
    mt <- synthType' tm
    case mt of
      Just t -> subtype t ty
      Nothing -> return False

subtype :: CType a -> CType a -> ScopeGen Bool
subtype ty1 ty2 = do
  ctx <- gets context
  wf1 <- checkTypeWF (ctypeToPoly ty1)
  wf2 <- checkTypeWF (ctypeToPoly ty2)
  st <- case (ty1, ty2) of
    (TyVar n, TyVar n') -> return $ n == n'
    (TyUnit, TyUnit) -> return True
    (TyExists n, TyExists n') -> return $ n == n' && n `elem` existentials ctx
    (TyArrow a1 a2, TyArrow b1 b2) -> do
      ctx' <- gets context
      st1 <- subtype b1 a1
      st2 <- subtype <$> apply (ctypeToPoly a2) <*> apply (ctypeToPoly b2)
      modify (\s -> s {context = ctx'})
      (&&) st1 <$> st2
    (a, TyForall ty) -> do
      ctx' <- gets context
      freeCnt <- gets freeCount
      let alpha = freeCnt
      let ctx'' = CtxForall alpha : ctx'
      modify (\s -> s {context = ctx''})
      st <- subtype a (typeSubst (TyI 0) (TyVar (TyN alpha)) ty)
      dropMarker (CtxForall alpha)
      return st
    (TyForall ty, a) -> do
      ctx' <- gets context
      freeCnt <- gets freeCount
      let alpha = freeCnt
      let ctx'' = CtxExist alpha : CtxMarker alpha : ctx'
      modify (\s -> s {context = ctx''})
      st <- subtype (typeSubst (TyI 0) (TyVar (TyN alpha)) ty) a
      dropMarker (CtxMarker alpha)
      return st
    (TyExists n, a) -> do
      ctx' <- gets context
      (&&)
        ( (n `elem` existentials ctx')
            && n `notElem` freeTyVars a
        )
        <$> instantiateL n (ctypeToPoly a)
    (a, TyExists n) -> do
      ctx' <- gets context
      (&&)
        ( (n `elem` existentials ctx')
            && n `notElem` freeTyVars a
        )
        <$> instantiateR (ctypeToPoly a) n
    _ -> return False
  return $ wf1 && wf2 && st

solve :: FreeName -> CType a -> ScopeGen Bool
solve alpha a = case ctypeToMono a of
  Just t -> do
    ctx <- gets context
    let ctxToAdd = [CtxExistSolved alpha t]
    let ctx' = replaceCtxExistWith ctx (CtxExist alpha) ctxToAdd
    modify (\s -> s {context = ctx'})
    return True
  Nothing -> return False

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
    (TyI 0) -> TyForall ty1
    (TyI n) -> TyForall (typeSubst (TyI (n -1)) ty' ty1)
    _ -> TyForall (typeSubst i ty' ty1)

freeTyVars :: CType a -> S.Set FreeName
freeTyVars ty = case ty of
  TyUnit -> S.empty
  TyVar (TyN n) -> S.singleton n
  TyVar (TyI _) -> S.empty
  TyForall t -> freeTyVars t
  TyExists n -> S.singleton n
  TyArrow ty1 ty2 -> S.union (freeTyVars ty1) (freeTyVars ty2)
