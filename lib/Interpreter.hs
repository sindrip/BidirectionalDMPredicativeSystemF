module Interpreter (interpret) where

import Parser

data Value
  = ValAbs Name Type Term
  | ValUnit
  deriving (Eq)

instance Show Value where
  show (ValAbs n ty tm) = "(λ" ++ n ++ " : " ++ show ty ++ " . " ++ show tm ++ ")"
  show ValUnit = "unit"

isValue :: Term -> Bool
isValue (TmAbs _ _ _) = True
isValue TmUnit = True
isValue _ = False

subst :: Name -> Term -> Term -> Term
subst x v t@(TmVar n)
  | x == n = v
  | otherwise = t
subst x v (TmAbs n ty tm) = TmAbs n ty (subst x v tm)
subst x v (TmApp tm1 tm2) = TmApp (subst x v tm1) (subst x v tm2)
subst _ _ TmUnit = TmUnit

interpret :: Term -> Maybe Term
interpret (TmVar _) = Nothing
interpret t@(TmAbs n ty tm) = Just t
interpret (TmApp (TmAbs n _ v) tm) = Just (subst n v tm)
interpret (TmApp tm1 tm2) =
  if isValue tm1 then
    case interpret tm2 of
      Nothing -> Nothing
      Just x -> Just (TmApp tm1 x)
  else
    case interpret tm1 of
      Nothing -> Nothing
      Just x -> Just (TmApp x tm2)
interpret TmUnit = Just TmUnit
