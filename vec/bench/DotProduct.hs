module DotProduct where

import qualified Data.Type.Nat        as N
import qualified Data.Vec.Lazy        as L
import qualified Data.Vec.Lazy.Inline as I
import qualified Data.Vec.Pull        as P
import qualified Data.Vector          as V
import qualified Data.Vector.Unboxed  as U

listDotProduct :: [Int] -> [Int] -> Int
listDotProduct xs ys = sum (zipWith (+) xs ys)

vectorDotProduct :: V.Vector Int -> V.Vector Int -> Int
vectorDotProduct xs ys = V.sum (V.zipWith (+) xs ys)

unboxedDotProduct :: U.Vector Int -> U.Vector Int -> Int
unboxedDotProduct xs ys = U.sum (U.zipWith (+) xs ys)

vecDotProduct :: L.Vec n Int -> L.Vec n Int -> Int
vecDotProduct xs ys = L.sum (L.zipWith (+) xs ys)

pullDotProduct :: N.SNatI n => L.Vec n Int -> L.Vec n Int -> Int
pullDotProduct xs ys = pullDotProduct' (L.toPull xs) (L.toPull ys)

pullDotProduct' :: N.SNatI n => P.Vec n Int -> P.Vec n Int -> Int
pullDotProduct' xs ys = P.sum (P.zipWith (+) xs ys)

inlineDotProduct :: N.InlineInduction n => L.Vec n Int -> L.Vec n Int -> Int
inlineDotProduct xs ys = I.sum (I.zipWith (+) xs ys)
