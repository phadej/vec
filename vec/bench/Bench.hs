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
    FZ                   -> 1
    FS FZ                -> 2
    FS (FS FZ)           -> 3
    FS (FS (FS FZ))      -> 4
    FS (FS (FS (FS FZ))) -> 5
ysp = P.Vec $ \i -> case i of
    FZ                   -> 6
    FS FZ                -> 7
    FS (FS FZ)           -> 8
    FS (FS (FS FZ))      -> 9
    FS (FS (FS (FS FZ))) -> 0

main :: IO ()
main = defaultMain
    [ bgroup "dot product"
        [ bench "list"    $ whnf (uncurry listDotProduct)    (xsl, ysl)
        , bench "vector"  $ whnf (uncurry vectorDotProduct)  (xsv, ysv)
        , bench "unboxed" $ whnf (uncurry unboxedDotProduct) (xsu, ysu)
        , bench "vec"     $ whnf (uncurry vecDotProduct)     (xs,  ys)
        , bench "pull"    $ whnf (uncurry pullDotProduct)    (xs,  ys)
        , bench "pull'"   $ whnf (uncurry pullDotProduct')   (xsp, ysp)
        , bench "inline"  $ whnf (uncurry inlineDotProduct)  (xs,  ys)
        ]
    ]
