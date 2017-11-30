{-# LANGUAGE GADTs, DataKinds, RankNTypes, ScopedTypeVariables, BangPatterns #-}
module Universe where

import Data.Proxy
import Data.Functor.Compose
import Data.Coerce
import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Vec.Lazy as L
import qualified Data.Vec.Pull as P

intReify :: forall r. Int -> (forall n. N.SNatI n => Proxy n -> r) -> r
intReify n k
  | n <= 0    = k (Proxy :: Proxy 'N.Z)
  | otherwise = intReify (n - 1) $ \(_ :: Proxy m) -> k (Proxy :: Proxy ('N.S m))

listUniverse :: Int -> [Int]
listUniverse = go 0 where
  go n m | m <= 0    = []
         | otherwise = n : go (n + 1) (m - 1)

linearUniverse :: forall n. N.SNatI n => L.Vec n (F.Fin n)
linearUniverse = go F.Z F.S (N.snat :: N.SNat n) where
  go :: forall f m.
        (forall p. f ('N.S p))
     -> (forall p. f p -> f ('N.S p))
     -> N.SNat m
     -> L.Vec m (f m)
  go _ _ N.SZ = L.VNil
  go i s N.SS = i L.::: coerce (go (Compose $ s i) (Compose . s . getCompose) N.snat)

length' :: L.Vec n a -> Int
length' = L.foldl' (\a _ -> a + 1) 0

finToInt :: F.Fin n -> Int
finToInt = go 0 where
  go :: Int -> F.Fin n -> Int
  go !a  F.Z    = a
  go  a (F.S i) = go (a + 1) i

sum' :: L.Vec n (F.Fin m) -> Int
sum' = L.foldl' (\a x -> a + finToInt x) 0

listIntLengthUniverse :: Int -> Int
listIntLengthUniverse = length . listUniverse

listLengthUniverse :: Int -> Int
listLengthUniverse n = intReify n $ \(_ :: Proxy n) ->
  length (F.universe :: [F.Fin n])

vecLengthUniverse :: Int -> Int
vecLengthUniverse n = intReify n $ \(_ :: Proxy n) ->
  length' (L.universe :: L.Vec n (F.Fin n))

vecPullLengthUniverse :: Int -> Int
vecPullLengthUniverse n = intReify n $ \(_ :: Proxy n) ->
  length' (L.fromPull (P.universe :: P.Vec n (F.Fin n)))

vecLinearLengthUniverse :: Int -> Int
vecLinearLengthUniverse n = intReify n $ \(_ :: Proxy n) ->
  length' (linearUniverse :: L.Vec n (F.Fin n))

pullLengthUniverse :: Int -> Int
pullLengthUniverse n = intReify n $ \(_ :: Proxy n) ->
  P.length (P.universe :: P.Vec n (F.Fin n))

listIntSumUniverse :: Int -> Int
listIntSumUniverse = sum . listUniverse

listSumUniverse :: Int -> Int
listSumUniverse n = intReify n $ \(_ :: Proxy n) ->
  sum $ map fromIntegral (F.universe :: [F.Fin n])

vecSumUniverse :: Int -> Int
vecSumUniverse n = intReify n $ \(_ :: Proxy n) ->
  sum' (L.universe :: L.Vec n (F.Fin n))

vecPullSumUniverse :: Int -> Int
vecPullSumUniverse n = intReify n $ \(_ :: Proxy n) ->
  sum' (L.fromPull (P.universe :: P.Vec n (F.Fin n)))

vecLinearSumUniverse :: Int -> Int
vecLinearSumUniverse n = intReify n $ \(_ :: Proxy n) ->
  sum' (linearUniverse :: L.Vec n (F.Fin n))

pullSumUniverse :: Int -> Int
pullSumUniverse n = intReify n $ \(_ :: Proxy n) ->
  P.foldl' (\a x -> a + finToInt x) 0 (P.universe :: P.Vec n (F.Fin n))
