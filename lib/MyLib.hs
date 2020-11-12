module MyLib (someFunc) where

data Term
  = Var String
  | Abs String Type Term
  | App Term Term
  | Unit

data Type
  = Arrow Type Type
  | UnitT

-- data Context = Empty | Ctx (String, Type) Context

someFunc :: IO ()
someFunc = putStrLn "someFunc"
