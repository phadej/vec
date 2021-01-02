{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Main (main) where

import Data.Fin           (Fin (..))
import Data.Function      (fix)
import Data.Proxy         (Proxy (..))
import Data.Tagged        (Tagged (..), retag)
import Data.Type.Equality
import GHC.Generics       (Generic)
import Test.Inspection

import qualified Data.Fin      as F
import qualified Data.Fin.Enum as E
import qualified Data.Type.Nat as N

import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- SNatI
-------------------------------------------------------------------------------

-- | This doesn't evaluate compile time.
lhsInline :: Int
lhsInline = unTagged (N.induction1 (pure 0) (retag . fmap succ) :: Tagged N.Nat5 Int)

-- | This doesn't evaluate compile time.
lhsNormal :: Int
lhsNormal = unTagged (manualInduction1 (pure 0) (retag . fmap succ) :: Tagged N.Nat5 Int)

--- | Induction on 'Nat'.
manualInduction1
     :: forall n f a. N.SNatI n
     => f 'N.Z a                                        -- ^ zero case
     -> (forall m. N.SNatI m => f m a -> f ('N.S m) a)  -- ^ induction step
     -> f n a
manualInduction1 z f = go where
    go :: forall m. N.SNatI m => f m a
    go = case N.snat :: N.SNat m of
        N.SZ -> z
        N.SS -> f go

rhs :: Int
rhs = 5

inspect $ 'lhsInline === 'rhs
inspect $ 'lhsNormal =/= 'rhs

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

-- | Note: GHC 8.0 (but not GHC 8.2?) seems to be
-- so smart, it reuses dictionary value.
--
-- Therefore, we define own local Ordering'
data Ordering' = LT' | EQ' | GT' deriving (Generic)

lhsEnum :: Ordering' -> F.Fin N.Nat3
lhsEnum = E.gfrom

rhsEnum :: Ordering' -> F.Fin N.Nat3
rhsEnum LT' = FZ
rhsEnum EQ' = FS FZ
rhsEnum GT' = FS (FS FZ)

inspect $ 'lhsEnum ==- 'rhsEnum

-------------------------------------------------------------------------------
-- Proofs
-------------------------------------------------------------------------------

lhsProof :: forall n. N.SNatI n => F.Fin (N.Mult n N.Nat1) -> F.Fin n
lhsProof x = case N.proofMultNOne :: N.Mult n N.Nat1 :~: n of
    Refl -> x

rhsProof :: forall n. N.SNatI n => F.Fin (N.Mult n N.Nat1) -> F.Fin n
rhsProof x = unsafeCoerce x

inspect $ 'lhsProof ==- 'rhsProof

-------------------------------------------------------------------------------
-- unfoldedFix
-------------------------------------------------------------------------------

foldrF :: (a -> b -> b) -> b -> ([a] -> b) -> [a] -> b
foldrF _f  z _go []     = z
foldrF  f _z  go (x : xs) = f x (go xs)

superfold :: [Int] -> Int
superfold = N.unfoldedFix (Proxy :: Proxy N.Nat5) (foldrF (+) 0)

-- Note: we need to write list explicitly, cannot use shorthand [1..4]
-- 'enumFromTo' is a recursive function!
--
-- Try to change [1,2,4,] to [1..4] to see the generated core :)
lhsFold :: Int
lhsFold = superfold [1,2,3,4]

lhsFold' :: Int
lhsFold' = fix (foldrF (+) 0) [1,2,3,4]

rhsFold :: Int
rhsFold = 10

inspect $ 'lhsFold  === 'rhsFold
inspect $ 'lhsFold' =/= 'rhsFold

lhsUnfold :: (a -> a) -> a
lhsUnfold f = N.unfoldedFix (Proxy :: Proxy N.Nat3) f

rhsUnfold :: (a -> a) -> a
rhsUnfold f = f (f (f (fix f)))

inspect $  'lhsUnfold === 'rhsUnfold

-------------------------------------------------------------------------------
-- Power
-------------------------------------------------------------------------------

power :: forall n. N.SNatI n => Proxy n -> Int -> Int
power _ k = unTagged impl where
    impl :: Tagged n Int
    impl = N.induction1 (Tagged 1) $ \(Tagged rec') -> Tagged (rec' * k)

lhsPower5 :: Int -> Int
lhsPower5 = power (Proxy :: Proxy N.Nat5)

rhsPower5 :: Int -> Int
rhsPower5 k = k * k * k * k * k

inspect $ 'lhsPower5 === 'rhsPower5

-------------------------------------------------------------------------------
-- Main to make GHC happy
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
