{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module TypeChecker where

data Name
  = Global String
  | Local Int
  deriving (Show, Eq)

type Idx = Int

data TypeCategory = Monotype | Polytype
  deriving (Show, Eq)

data CType :: TypeCategory -> * where
  TyArrow :: CType a -> CType a -> CType a
  TyUnit :: CType a
  TyVar :: Name -> CType a
  TyExists :: Name -> CType a
  TyForall :: Name -> CType 'Polytype -> CType 'Polytype

-- data CTypeLinear

-- TypeClass Types

deriving instance Show (CType a)

deriving instance Eq (CType a)

type Context a = [(Name, CType a)]

data Term a
  = Ann (Term a) (CType a)
  | Free Name
  | Bound Idx
  | Unit
  | App (Term a) (Term a)
  | Abs (Term a)
  deriving (Show, Eq)

-- zero :: Term
-- zero = TmAbs "f" TyUnit (TmAbs "x" TyUnit (TmVar "x" 0))

zero :: (Term a)
zero = Abs (Abs (Bound 0))

synthType :: Context a -> Term a -> Maybe (CType a)
synthType = synthType' 0

synthType' :: Int -> Context a -> Term a -> Maybe (CType a)
synthType' i ctx (Ann tm ty) =
  if checkType i ctx tm ty
    then Just ty
    else Nothing
synthType' _ _ Unit = Just TyUnit
synthType' _ ctx (Free n) = lookup n ctx
synthType' i ctx (App ts tc) =
  case synthType' i ctx ts of
    Just (TyArrow ty1 ty2) -> if checkType i ctx tc ty1 then Just ty2 else Nothing
    _ -> Nothing
synthType' _ _ _ = Nothing

-- todo forall/exists
checkType :: Int -> Context a -> Term a -> CType a -> Bool
checkType i ctx (Abs tm) (TyArrow ty1 ty2) =
  checkType (i + 1) ((Local i, ty1) : ctx) (subst 0 (Free (Local i)) tm) ty2
checkType i ctx tm ty = case synthType' i ctx tm of
  Just infTy -> infTy == ty
  Nothing -> False

subst :: Int -> Term a -> Term a -> Term a
subst i tm1 (Ann tm2 ty) = Ann (subst i tm1 tm2) ty
subst i tm1 (Abs tm2) = Abs (subst (i + 1) tm1 tm2)
subst i tm (Bound j) = if i == j then tm else Bound j
subst _ _ (Free y) = Free y
subst i tm (App tm1 tm2) = App (subst i tm tm1) (subst i tm tm2)
subst _ _ Unit = Unit