{-# LANGUAGE GADTs #-}
module Main (main) where

import Criterion.Main

import Data.Fin      (Fin (..))
import Data.Type.Nat (Nat5)
import Data.Vec.Lazy (Vec (..))

import qualified Data.Vec.Pull       as P
import qualified Data.Vector         as V
import qualified Data.Vector.Unboxed as U

import DotProduct
import Universe

xsl, ysl :: [Int]
xsl = [1,2,3,4,5]
ysl = [6,7,8,9,0]

xsv, ysv :: V.Vector Int
xsv = V.fromList xsl
ysv = V.fromList ysl

xsu, ysu :: U.Vector Int
xsu = U.fromList xsl
ysu = U.fromList ysl

xs, ys :: Vec Nat5 Int
xs = 1 ::: 2 ::: 3 ::: 4 ::: 5 ::: VNil
ys = 6 ::: 7 ::: 8 ::: 9 ::: 0 ::: VNil

xsp, ysp :: P.Vec Nat5 Int
xsp = P.Vec $ \i -> case i of
    Z               -> 1
    S Z             -> 2
    S (S Z)         -> 3
    S (S (S Z))     -> 4
    S (S (S (S Z))) -> 5
ysp = P.Vec $ \i -> case i of
    Z               -> 6
    S Z             -> 7
    S (S Z)         -> 8
    S (S (S Z))     -> 9
    S (S (S (S Z))) -> 0

main :: IO ()
main = defaultMain
    [ bgroup "dot product"
        [ bench "list"    $ whnf (uncurry listDotProduct)    (xsl, ysl)
        , bench "vector"  $ whnf (uncurry vectorDotProduct)  (xsv, ysv)
        , bench "unboxed" $ whnf (uncurry unboxedDotProduct) (xsu, ysu)
        , bench "vec"     $ whnf (uncurry vecDotProduct)     (xs,  ys)
        , bench "vec'"    $ whnf (uncurry vecDotProduct')    (xs,  ys)
        , bench "pull"    $ whnf (uncurry pullDotProduct)    (xs,  ys)
        , bench "pull'"   $ whnf (uncurry pullDotProduct')   (xsp, ysp)
        , bench "inline"  $ whnf (uncurry inlineDotProduct)  (xs,  ys)
        ]
    , bgroup "length/universe"
        [ bench "listInt"   $ whnf listIntLengthUniverse   1000
        , bench "list"      $ whnf listLengthUniverse      1000
        , bench "vec"       $ whnf vecLengthUniverse       1000
        , bench "vecLinear" $ whnf vecLinearLengthUniverse 1000
        , bench "vecPull"   $ whnf vecPullLengthUniverse   1000
        , bench "pull"      $ whnf pullLengthUniverse      1000
        ]
    , bgroup "sum/universe"
        [ bench "listInt"   $ whnf listIntSumUniverse   100
        , bench "list"      $ whnf listSumUniverse      100
        , bench "vec"       $ whnf vecSumUniverse       100
        , bench "vecLinear" $ whnf vecLinearSumUniverse 100
        , bench "vecPull"   $ whnf vecPullSumUniverse   100
        , bench "pull"      $ whnf pullSumUniverse      100
        ]
    ]
