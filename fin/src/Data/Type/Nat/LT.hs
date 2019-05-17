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

{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
module Data.Type.Nat.LT (
    LT (..),
    LTProof (..),
    -- * Lemmas
    ltReflAbsurd,
    ltSymAbsurd,
    ltTrans,
    ) where

import qualified Data.Type.Nat as N

import GHC.Exts (Constraint)

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

ltZeroAbsurd :: LTProof x 'N.Z -> a
ltZeroAbsurd p = case p of {}

ltSucc :: LTProof n m -> LTProof n ('N.S n)
ltSucc = undefined

-------------------------------------------------------------------------------
-- WT
-------------------------------------------------------------------------------

newtype Acc (rel :: k -> k -> *) (x :: k) =
    MkAcc { unAcc :: forall y. rel y x -> Acc rel y }

data P :: N.Nat -> N.Nat -> * where
    LTRefl :: P n ('N.S n)
    LTSucc :: P n m -> P n ('N.S m)

ltWellFounded :: Acc P n
ltWellFounded = MkAcc ltWellFounded'

ltWellFounded' :: P y n -> Acc  P y
ltWellFounded' LTRefl     = ltWellFounded
ltWellFounded' (LTSucc p) = ltWellFounded' p

bar :: N.SNat n -> Acc P n -> Int
bar N.SZ _   = 0
bar N.SS acc = bar' acc

bar' :: forall n. N.SNatI n => Acc P ('N.S n) -> Int
bar' acc = bar (N.snat :: N.SNat n) (unAcc acc LTRefl)

{-
ltWellFounded' :: forall n. N.SNatI n => Acc N.SNatI LTProof n
ltWellFounded' = case N.snat :: N.SNat n of
    N.SZ -> MkAcc ltZeroAbsurd 
    N.SS -> MkAcc foo

foo :: forall y x. (N.SNatI y, N.SNatI x) => LTProof y ('N.S x) -> Acc N.SNatI LTProof y
foo LTZ     = ltWellFounded'
foo (LTS p) = unAcc (ltWellFounded' @x) (bar p)

bar :: LTProof n m -> LTProof ('N.S n) m
bar = undefined
-}
