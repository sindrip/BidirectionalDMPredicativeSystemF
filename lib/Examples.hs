module Examples where

import Types

test :: Term
test = Abs (Var (TmI 0))

zeroU :: Term
zeroU = Abs (Abs (Ann (Var (TmI 0)) TyUnit))

zero :: Term
zero = Abs (Abs (Var (TmI 0)))

suc :: Term
suc = Abs (Abs (Abs (App (Var (TmI 1)) (App (App (Var (TmI 2)) (Var (TmI 1))) (Var (TmI 0))))))

one :: Term
one = App suc zero

add :: Term
add = Abs (Abs (Abs (Abs (App (App (Var (TmI 3)) (Var (TmI 1))) (App (App (Var (TmI 2)) (Var (TmI 1))) (Var (TmI 0)))))))

eid :: Term
eid = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 0)) (TyVar (TyI 0))))

eidFail :: Term
eidFail = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 0)) TyUnit))

eidFail2 :: Term
eidFail2 = Ann (Abs (Var (TmI 0))) (TyForall (TyArrow (TyVar (TyI 1)) (TyVar (TyI 0))))
