-- Based upon https://markkarpov.com/tutorial/megaparsec.html
{-# LANGUAGE OverloadedStrings #-}

module Parser (Name,Type(..),Term(..)) where

import Control.Monad.Combinators.Expr
import Data.Text (Text)
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

ws :: Parser ()
ws =
  L.space
    space1
    empty
    empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: Text -> Parser Text
symbol = L.symbol ws

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

type Name = String

data Type
  = TyArrow Type Type
  | TyUnit
  | TyVar Name
  deriving (Eq)

data Term
  = TmVar Name
  | TmAbs Name Type Term
  | TmApp Term Term
  | TmUnit
  deriving (Eq)

instance Show Type where
  show (TyArrow t1 t2) = "(" ++ show t1 ++ " → " ++ show t2 ++ ")"
  show TyUnit = "Unit"
  show (TyVar n) = n

instance Show Term where
  show (TmVar n) = n
  show (TmAbs n ty tm) = "(λ" ++ n ++ " : " ++ show ty ++ " . " ++ show tm ++ ")"
  show (TmApp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show TmUnit = "unit"

pName :: Parser Name
pName = lexeme $ (:) <$> letterChar <*> many alphaNumChar

pAtomTy :: Parser Type
pAtomTy = do
  n <- pName
  case n of
    "Unit" -> return TyUnit
    _ -> return $ TyVar n

pTypeTerm :: Parser Type
pTypeTerm =
  choice
    [ parens pType,
      pAtomTy
    ]

opTableTy :: [[Operator Parser Type]]
opTableTy =
  [ [InfixR (TyArrow <$ symbol "->")]
  ]

pType :: Parser Type
pType = makeExprParser pTypeTerm opTableTy

pAbs :: Parser Term
pAbs = do
  _ <- lexeme "/"
  n <- pName
  _ <- lexeme ":"
  ty <- pType
  _ <- lexeme "."
  TmAbs n ty <$> pTerm

pAtom :: Parser Term
pAtom = do
  n <- pName
  case n of
    "unit" -> return TmUnit
    _ -> return $ TmVar n

pTermNonApp :: Parser Term
pTermNonApp = choice
 [
     parens pTerm,
     pAbs,
     pAtom
 ]

opTableTm :: [[Operator Parser Term]]
opTableTm =
  [ [InfixL (TmApp <$ symbol ".")]
  ]

pTerm :: Parser Term
pTerm = makeExprParser pTermNonApp opTableTm
