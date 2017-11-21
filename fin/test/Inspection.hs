{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Main (main) where

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
-- InlineInduction
-------------------------------------------------------------------------------

-- | This doesn't evaluate compile time.
lhsInline :: Int
lhsInline = unTagged (N.inlineInduction1 (pure 0) (retag . fmap succ) :: Tagged N.Nat5 Int)

-- | This doesn't evaluate compile time.
lhsNormal :: Int
lhsNormal = unTagged (N.induction1 (pure 0) (retag . fmap succ) :: Tagged N.Nat5 Int)

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
rhsEnum LT' = F.Z
rhsEnum EQ' = F.S F.Z
rhsEnum GT' = F.S (F.S F.Z)

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
-- Main to make GHC happy
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
