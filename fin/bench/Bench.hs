{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators, DataKinds, GADTs #-}
module Main (main) where

import Criterion.Main (defaultMain, bench, whnf)

import Data.Type.Nat
import Data.Type.Equality

import qualified Data.Type.Dec as C
import qualified Data.Type.NewDec as R

lhs :: SNat (Mult Nat9 Nat8)
lhs = snat

rhs :: SNat (Mult Nat9 Nat8)
rhs = snat

main :: IO ()
main = defaultMain
    [ bench "Classical Dec" $ whnf (C.decToBool . classic)  (lhs, rhs)
    , bench "Reflects  Dec" $ whnf (R.decToBool . reflects) (lhs, rhs)
    , bench "Equality"      $ whnf equality                 (lhs, rhs)
    ]

classic :: (SNat n, SNat m) -> C.Dec (n :~: m)
classic ~(n,m) = withSNat n $ withSNat m discreteNat

reflects :: (SNat n, SNat m) -> R.Dec (n :~: m)
reflects ~(n,m) = withSNat n $ withSNat m discreteNat'

equality :: (SNat n, SNat m) -> Bool
equality ~(n,m) = go n m where
    go :: SNat x -> SNat y -> Bool
    go SZ SZ = True
    go SS SZ = False
    go SZ SS = False
    go x@SS y@SS = go' x y

    go' :: forall x y. SNat ('S x) -> SNat ('S y) -> Bool
    go' SS SS = go (snat :: SNat x) (snat :: SNat y)
