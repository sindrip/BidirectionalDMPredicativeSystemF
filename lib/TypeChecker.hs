module TypeChecker where

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

type Idx = Int

data CKind = Star
  deriving (Show)

data CType
  = TyArrow CType CType
  | TyUnit
  | TyVar Name
  deriving (Show, Eq)

data Info
  = HasKind CKind
  | HasType CType

type Context = [(Name, Info)]

data TermSynth
  = Ann TermCheck CType
  | Free Name
  | Bound Idx
  | Unit
  | App TermSynth TermCheck
  deriving (Show, Eq)

data TermCheck
  = Inf TermSynth
  | Abs TermCheck
  deriving (Show, Eq)

-- zero :: Term
-- zero = TmAbs "f" TyUnit (TmAbs "x" TyUnit (TmVar "x" 0))

zero :: TermCheck
zero = Abs (Abs (Inf (Bound 0)))

checkKind :: Context -> CType -> CKind -> Bool
checkKind _ TyUnit Star = True
checkKind ctx (TyArrow t1 t2) Star = checkKind ctx t1 Star && checkKind ctx t2 Star
checkKind _ _ _ = False

synthType :: Context -> TermSynth -> Maybe CType
synthType = synthType' 0

synthType' :: Int -> Context -> TermSynth -> Maybe CType
synthType' i ctx (Ann tm ty) =
  if checkKind ctx ty Star && checkType i ctx tm ty
    then Just ty
    else Nothing
synthType' _ _ Unit = Just TyUnit
synthType' i ctx (Free n) =
  case lookup n ctx of
    Just (HasType ty) -> Just ty
    _ -> Nothing
synthType' i ctx (App ts tc) =
  case synthType' i ctx ts of
    Just (TyArrow ty1 ty2) -> if checkType i ctx tc ty1 then Just ty2 else Nothing
    _ -> Nothing
synthType' _ _ _ = Nothing

checkType :: Int -> Context -> TermCheck -> CType -> Bool
checkType i ctx (Inf e) ty =
  case synthType' i ctx e of
    Just t -> t == ty
    Nothing -> False
checkType i ctx (Abs tm) (TyArrow ty1 ty2) =
  checkType (i + 1) ((Local i, HasType ty1) : ctx) (checkSubst 0 (Free (Local i)) tm) ty2
checkType _ _ _ _ = False

synthSubst :: Int -> TermSynth -> TermSynth -> TermSynth
synthSubst i tm1 (Ann tm2 ty) = Ann (checkSubst i tm1 tm2) ty
synthSubst i tm (Bound j) = if i == j then tm else Bound j
synthSubst _ _ (Free y) = Free y
synthSubst i tm (App tm1 tm2) = App (synthSubst i tm tm1) (checkSubst i tm tm2)
synthSubst _ _ Unit = Unit

checkSubst :: Int -> TermSynth -> TermCheck -> TermCheck
checkSubst i tm1 (Inf tm2) = Inf (synthSubst i tm1 tm2)
checkSubst i tm1 (Abs tm2) = Abs (checkSubst (i + 1) tm1 tm2)