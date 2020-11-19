-- Based upon https://markkarpov.com/tutorial/megaparsec.html
{-# LANGUAGE OverloadedStrings #-}

module Parser (Name,Type(..),Term(..)) where

import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Data.List (elemIndex)
import Data.Text (Text)
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- type Parser = Parsec Void Text
type Parser = ParsecT Void Text (Reader [String])

bind :: String -> Parser a -> Parser a
bind x = local (x :)

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

type Idx = Int

data Type
  = TyArrow Type Type
  | TyUnit
  | TyVar Name
  deriving (Eq)

data Term
  = TmVar Name Idx
  | TmAbs Name Type Term
  | TmApp Term Term
  | TmUnit
  deriving (Eq)

instance Show Type where
  show (TyArrow t1 t2) = "(" ++ show t1 ++ " → " ++ show t2 ++ ")"
  show TyUnit = "Unit"
  show (TyVar n) = n

instance Show Term where
  show (TmVar n i) = n ++ "(" ++ show i ++ ")"
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
  _ <- symbol "/"
  n <- pName
  exists <- asks (elem n)
  -- Add parse error if binding variable is shadowed
  when exists $ fail $ n ++ " already bound"
  _ <- symbol ":"
  ty <- pType
  _ <- symbol "."
  tm <- bind n pTerm
  return $ TmAbs n ty tm

pAtom :: Parser Term
pAtom = do
  n <- pName
  if n == "unit"
    then return TmUnit
    else do
      i <- asks (elemIndex n)
      case i of
        Nothing -> return $ TmVar n (-1)
        Just v -> return $ TmVar n v

pTermNonApp :: Parser Term
pTermNonApp =
  choice
    [ parens pTerm,
      pAbs,
      pAtom
    ]

opTableTm :: [[Operator Parser Term]]
opTableTm =
  [ [InfixL (TmApp <$ symbol ".")]
  ]

pTerm :: Parser Term
pTerm = makeExprParser pTermNonApp opTableTm
