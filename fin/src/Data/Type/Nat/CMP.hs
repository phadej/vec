{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Type.Nat.CMP (
    CMP,
    WithOrdering,
    -- * Lemmas
    ltCmpGT,
    ltCmpLT,
    )  where

import Data.Type.Equality
import Data.Type.Nat.LT

import qualified Data.Type.Nat as N

-- | Comparison function for type-level 'N.Nat'.
type family CMP (n :: N.Nat) (m :: N.Nat) :: Ordering where
    CMP  'N.Z     'N.Z    = 'EQ
    CMP  'N.Z    ('N.S m) = 'LT
    CMP ('N.S n)  'N.Z    = 'GT
    CMP ('N.S n) ('N.S m) = CMP n m

-- | An eliminator of 'Ordering' on a type level.
type family WithOrdering (o :: Ordering) (a :: k) (b :: k) (c :: k) :: k where
    WithOrdering 'LT a b c = a
    WithOrdering 'EQ a b c = b
    WithOrdering 'GT a b c = c

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

ltCmpLT :: LTProof n m -> CMP n m :~: 'LT
ltCmpLT LTZ      = Refl
ltCmpLT (LTS lt) = case ltCmpLT lt of Refl -> Refl

ltCmpGT :: LTProof n m -> CMP m n :~: 'GT
ltCmpGT LTZ      = Refl
ltCmpGT (LTS lt) = case ltCmpGT lt of Refl -> Refl
