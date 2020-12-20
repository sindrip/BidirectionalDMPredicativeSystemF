{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module TestRunner ( tests ) where

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck

import Types
import Test.QuickCheck
import Control.Monad

instance Arbitrary Term where
  arbitrary = sized arbTerm

arbTerm :: Int -> Gen Term
arbTerm 0 = oneof [ Var <$> arbitrary
                  , return Unit
                  ]
arbTerm n = oneof [ liftM2 Ann sTerm arbitrary
                  , Var <$> arbitrary
                  , return Unit
                  , liftM2 App sTerm sTerm
                  , Abs <$> sTerm
                  ]
  where sTerm = arbTerm (n `div` 2)

instance Arbitrary (CType Polytype) where
  arbitrary = sized arbType

arbType :: Int -> Gen (CType Polytype)
arbType 0 = oneof [ return TyUnit
                  , TyVar <$> arbitrary
                  , TyExists <$> arbitrary
                  ]
arbType n = oneof [ liftM2 TyArrow sType sType
                  , return TyUnit
                  , TyVar <$> arbitrary
                  , TyExists <$> arbitrary
                  , TyForall <$> sType
                  ]
            where sType = arbType (n `div` 2)

instance Arbitrary (CType Monotype) where
  arbitrary = sized arbMType

arbMType :: Int -> Gen (CType Monotype)
arbMType 0 = oneof [ return TyUnit
                  , TyVar <$> arbitrary
                  , TyExists <$> arbitrary
                  ]
arbMType n = oneof [ liftM2 TyArrow sType sType
                  , return TyUnit
                  , TyVar <$> arbitrary
                  , TyExists <$> arbitrary
                  ]
            where sType = arbMType (n `div` 2)


instance Arbitrary TyName where
  arbitrary = oneof [ TyI <$> arbitrary
                    , TyN <$> arbitrary
                    ]

instance Arbitrary TmName where
  arbitrary = oneof [ TmI <$> arbitrary
                    , TmN <$> arbitrary
                    ]

instance Arbitrary TyIdx where
  arbitrary = elements [TyIdx n | n <- [0..20]]

instance Arbitrary TmIdx where
  arbitrary = elements [TmIdx n | n <- [0..20]]

instance Arbitrary FreeName where
  arbitrary = elements [FreeName n | n <- [0..20]]

instance Arbitrary CtxElem where
  arbitrary = oneof [ CtxForall <$> arbitrary
                    , liftM2 CtxVar arbitrary arbitrary
                    , CtxExist <$> arbitrary
                    , liftM2 CtxExistSolved arbitrary arbitrary
                    , CtxMarker <$> arbitrary
                    ]

tests :: IO [Test]
tests = return [ typecastPoly
               ]

typecastPoly :: Test
typecastPoly = testGroup "Typecasting"
  [ testProperty "Typecasting to polytypes" (\t -> ctypeToPoly t == t)
  , testProperty "Typecasting to monotypes" (\t -> ctypeToMono t == Just t)
  ]
