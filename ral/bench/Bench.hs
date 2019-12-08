module Main where

import Criterion.Main (bench, bgroup, defaultMain, whnf)

import qualified Data.List            as L
import qualified Data.RAList          as R
import qualified Data.RAList.NonEmpty as NER
import qualified Data.Vector          as V
import qualified Data.Vector.Unboxed  as U

list :: [Int]
list = [1 .. 10000]

ralist :: R.RAList Int
ralist = R.fromList list

vector :: V.Vector Int
vector = V.fromList list

uvector :: U.Vector Int
uvector = U.fromList list

rlast :: R.RAList a -> a
rlast (R.NonEmpty r) = NER.last r
rlast R.Empty        = error "rlast Empty"

main :: IO ()
main = defaultMain
    [ bgroup "Last"
        [ bench "List"           $ whnf L.last list
        , bench "RAList"         $ whnf  rlast ralist
        , bench "Vector"         $ whnf V.last vector
        , bench "Vector.Unboxed" $ whnf U.last uvector
        ]
    , bgroup "Index"
        [ bench "List"           $ whnf (\xs -> xs L.!! (L.length xs - 1)) list
        , bench "RAList"         $ whnf (\xs -> xs R.!  (R.length xs - 1)) ralist
        , bench "Vector"         $ whnf (\xs -> xs V.!  (V.length xs - 1)) vector
        , bench "Vector.Unboxed" $ whnf (\xs -> xs U.!  (U.length xs - 1)) uvector
        ]
    , bgroup "Cons"
        [ bench "List"           $ whnf (0 :)      list
        , bench "RAList"         $ whnf (R.cons 0) ralist
        , bench "Vector"         $ whnf (V.cons 0) vector
        , bench "Vector.Unboxed" $ whnf (U.cons 0) uvector
        ]
    , bgroup "Length"
        [ bench "List"           $ whnf L.length list
        , bench "RAList"         $ whnf R.length ralist
        , bench "Vector"         $ whnf V.length vector
        , bench "Vector.Unboxed" $ whnf U.length uvector
        ]
    , bgroup "LastAfterCons"
        [ bench "List"           $ whnf (\xs -> L.last $ 0 : xs     ) list
        , bench "RAList"         $ whnf (\xs ->  rlast $ R.cons 0 xs) ralist
        , bench "Vector"         $ whnf (\xs -> V.last $ V.cons 0 xs) vector
        , bench "Vector.Unboxed" $ whnf (\xs -> U.last $ U.cons 0 xs) uvector
        ]
    ]
