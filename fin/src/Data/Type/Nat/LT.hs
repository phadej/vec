{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE UndecidableInstances #-}
module Data.Type.Nat.LT (
    LT (..),
    LTProof (..),
    -- * Lemmas
    ltReflAbsurd,
    ltSymAbsurd,
    ltTrans,
    ) where

import qualified Data.Type.Nat as N

-------------------------------------------------------------------------------
-- Proof
-------------------------------------------------------------------------------

data LTProof :: N.Nat -> N.Nat -> * where
    LTZ :: LTProof 'N.Z ('N.S m)
    LTS :: LTProof n m -> LTProof ('N.S n) ('N.S m)

deriving instance Show (LTProof n m)

-- | 'LTProof' values are unique.
instance Eq (LTProof n m) where
    _ == _ = True

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Less-Than-or. \(<\). Well-founded relation on 'Nat'.
--
-- GHC can solve this for us!
--
-- >>> ltProof :: LTProof N.Nat0 N.Nat4
-- LTZ
--
-- >>> ltProof :: LTProof N.Nat2 N.Nat4
-- LTS (LTS LTZ)
--
-- >>> ltProof :: LTProof N.Nat3 N.Nat3
-- ...
-- ...error...
-- ...
--
class LT (n :: N.Nat) (m :: N.Nat) where
    ltProof :: LTProof n m

instance m ~ 'N.S m' => LT 'N.Z m where
    ltProof = LTZ

instance (m ~ 'N.S m', LT n m') => LT ('N.S n) m where
    ltProof = LTS ltProof

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | \(\forall n : \mathbb{N}, n < n \to \bot \)
ltReflAbsurd :: LTProof n n -> a
ltReflAbsurd p = case p of
    LTS p' -> ltReflAbsurd p'

-- | \(\forall n\, m : \mathbb{N}, n < m \to m < n \to \bot \)
ltSymAbsurd :: LTProof n m -> LTProof m n -> a
ltSymAbsurd LTZ q           = case q of {}
ltSymAbsurd (LTS p) (LTS q) = ltSymAbsurd p q

-- | \(\forall n\, m\, p : \mathbb{N}, n < m \to m < p \to n < p \)
ltTrans
    :: LTProof n m
    -> LTProof m p
    -> LTProof n p
ltTrans LTZ     (LTS _) = LTZ
ltTrans (LTS p) (LTS q) = LTS (ltTrans p q)

-------------------------------------------------------------------------------
-- More lemmas
-------------------------------------------------------------------------------
