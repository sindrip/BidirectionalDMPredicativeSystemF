module Examples where

import Types

zero :: Term
zero = Abs (Abs (Var (TmI 0)))

eid :: Term
eid = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 0)) (TyVar (TyI 0))))

eidFail :: Term
eidFail = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 0)) TyUnit))

eidFail2 :: Term
eidFail2 = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 1)) (TyVar (TyI 0))))
