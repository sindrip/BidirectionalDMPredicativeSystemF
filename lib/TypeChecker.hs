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

existentials :: Context -> [TyName]
existentials = go
  where
    go [] = []
    go ((CtxExist n) : xs) = n : go xs
    go ((CtxExistSolved n _) : xs) = n : go xs
    go (_ : xs) = go xs

foralls :: Context -> [TyName]
foralls = go
  where
    go [] = []
    go ((CtxForall n) : xs) = n : go xs
    go (_ : xs) = go xs

vars :: Context -> [TmName]
vars = go
  where
    go [] = []
    go ((CtxVar n _) : xs) = n : go xs
    go (_ : xs) = go xs

markers :: Context -> [TyName]
markers = go
  where
    go [] = []
    go ((CtxMarker n) : xs) = n : go xs
    go (_ : xs) = go xs

lookupSolution :: Context -> TyName -> Maybe (CType 'Monotype)
lookupSolution [] _ = Nothing
lookupSolution (c : cs) n =
  case c of
    (CtxExistSolved vn ty) ->
      if vn == n
        then Just ty
        else lookupSolution cs n
    _ -> lookupSolution cs n

lookupTypeOfVar :: Context -> TmName -> Maybe (CType 'Polytype)
lookupTypeOfVar [] _ = Nothing
lookupTypeOfVar (c : cs) n =
  case c of
    (CtxVar vn ty) ->
      if vn == n
        then Just ty
        else lookupTypeOfVar cs n
    _ -> lookupTypeOfVar cs n

dropMarker :: CtxElem -> Context -> Context
dropMarker m ctx = tail $ dropWhile (/= m) ctx

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
    TyVar n -> return $ n `elem` foralls ctx
    TyUnit -> return True
    TyArrow a b -> liftA2 (&&) (typeWF a) (typeWF b)
    TyForall a -> do
      freeCnt <- gets freeCount
      let alpha = TyN freeCnt
      let ctx' = CtxForall alpha : ctx

      modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
      chk <- typeWF (typeSubst (TyI 0) (TyExists alpha) a)
      modify (\s -> s {freeCount = freeCnt, context = ctx})
      return chk
    TyExists n -> return $ n `elem` existentials ctx

apply :: Context -> CType 'Polytype -> CType 'Polytype
apply gamma ty = case ty of
  TyUnit -> TyUnit
  TyVar n -> TyVar n
  TyForall t -> TyForall (apply gamma t)
  tye@(TyExists n) ->
    case lookupSolution gamma n of
      Just t -> apply gamma (ctypeToPoly t)
      Nothing -> tye
  TyArrow ty1 ty2 -> TyArrow (apply gamma ty1) (apply gamma ty2)

comesBefore :: Context -> TyName -> TyName -> Bool
comesBefore gamma alpha beta =
  let l = dropMarker (CtxExist beta) gamma
   in alpha `elem` existentials l

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
    let alpha = TyN freeCnt
    let beta = TyN (freeCnt + 1)
    let ctx' = CtxExist beta : CtxExist alpha : CtxMarker alpha : ctx

    modify (\s -> s {freeCount = freeCnt + 2, context = ctx'})
    chk <- checkType tm (TyExists beta)
    modify (\s -> s {freeCount = freeCnt, context = ctx})

    if chk
      then return $ Just (TyArrow (TyExists alpha) (TyExists beta))
      else return Nothing

synthApplyType :: Term 'Polytype -> CType 'Polytype -> ScopeGen (Maybe (CType 'Polytype))
synthApplyType tm (TyForall ty) =
  do
    ctx <- gets context
    freeCnt <- gets freeCount
    let alpha = TyN freeCnt
    let ctx' = CtxExist alpha : ctx

    modify (\s -> s {freeCount = freeCnt + 1, context = ctx'})
    t <- synthApplyType tm (typeSubst (TyI 0) (TyExists alpha) ty)
    modify (\s -> s {freeCount = freeCnt, context = ctx})

    return t
synthApplyType tm (TyExists ty) =
  do
    ctx <- gets context
    freeCnt <- gets freeCount
    let alpha = TyN freeCnt
    let beta = TyN (freeCnt + 1)
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
-- Apply context as substitution
checkType tm ty =
  do
    mt <- synthType' tm
    case mt of
      Just t -> subtype t ty
      Nothing -> return False

subtype :: CType a -> CType a -> ScopeGen Bool
subtype = undefined

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
typeSubst i ty' (TyExists n) =
  if i == n
    then ty'
    else TyExists n
typeSubst i ty' (TyForall ty1) =
  case i of
    (TyI 0) -> TyForall ty1
    (TyI n) -> TyForall (typeSubst (TyI (n -1)) ty' ty1)
    _ -> TyForall (typeSubst i ty' ty1)
