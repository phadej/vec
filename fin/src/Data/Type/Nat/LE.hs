{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE UndecidableInstances #-}
module Data.Type.Nat.LE (
    LE (..),
    LEProof (..),
    -- * Lemmas
    leRefl,
    leAntiSym,
    leTrans,
    -- * More lemmas
    proofZeroLEZero,
    ) where

import Data.Type.Equality
import Data.Type.Nat

-------------------------------------------------------------------------------
-- Proof
-------------------------------------------------------------------------------

data LEProof n m where
    LEZ :: LEProof 'Z m
    LES :: LEProof n m -> LEProof ('S n) ('S m)

deriving instance Show (LEProof n m)

-- | 'LEProof' values are unique.
instance Eq (LEProof n m) where
    _ == _ = True

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Total order of 'Nat'. Less-than-or-Equal-to. \(\le\).
--
class LE n m where
    sle :: LEProof n m

instance LE 'Z m where
    sle = LEZ

instance (m ~ 'S m', LE n m') => LE ('S n) m where
    sle = LES sle

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | \(\forall n : \mathbb{N}, n \le n \)
leRefl :: forall n. SNatI n => LEProof n n
leRefl = case snat :: SNat n of
    SZ -> LEZ
    SS -> LES leRefl

-- | \(\forall n\, m : \mathbb{N}, n \le m \to m \le n \to n \equiv m \)
leAntiSym :: LEProof n m -> LEProof m n -> n :~: m
leAntiSym LEZ     LEZ     = Refl
leAntiSym (LES p) (LES q) = case leAntiSym p q of Refl -> Refl

-- | \(\forall n\, m\, p : \mathbb{N}, n \le m \to m \le p \to n \le p \)
leTrans
    :: LEProof n m
    -> LEProof m p
    -> LEProof n p
leTrans LEZ     _       = LEZ
leTrans (LES p) (LES q) = LES (leTrans p q)

-------------------------------------------------------------------------------
-- More lemmas
-------------------------------------------------------------------------------

-- | \(\forall n\ : \mathbb{N}, n \le 0 \to n \equiv 0 \)
proofZeroLEZero :: LEProof n 'Z -> n :~: 'Z
proofZeroLEZero LEZ = Refl

{-
-- | \(\forall n : \mathbb{N}, n \le 0 \to n \equiv 0\).
proofZeroLEZero :: forall n. LEProof n 'Z -> n :~: 'Z
proofZeroLEZero LEProofN = Refl

-- | \(\forall n : \mathbb{N}, 0 \le n\).
proofLEZeroN :: forall n. SNatI n => LEProof 'Z n
proofLEZeroN = case snat :: SNat n of
    SZ -> LEProofN
    SS -> LES proofLEZeroN

-- | \(\forall n\, m : \mathbb {N}. n \le m \to 1 + n \le 1 + m\)
proofLESucc :: LEProof n m -> LEProof ('S n) ('S m)
proofLESucc LEProofN     = LEProofN
proofLESucc (LES p) = LES (proofLESucc p)

-- | \(\forall n\, m : \mathbb{N}. 1 + n \le 1 + m \to n \le m\)
proofLESucc' :: forall n m. LEProof ('S n) ('S m) -> LEProof n m
proofLESucc' LEProofN     = LEProofN
proofLESucc' (LES p) = proofLEProofmma p

-- | \(\forall n\, m : \mathbb{N}. 1 + n \le m \to n \le m\)
proofLEProofmma  :: forall n m. LEProof ('S n) m -> LEProof n m
proofLEProofmma LEProofN = LES LEProofN
proofLEProofmma (LES p) = LES (proofLEProofmma p)

decideLEProof :: forall n m. (SNatI n, SNatI m) => Dec (LEProof n m)
decideLEProof = case snat :: SNat n of
    SZ -> Yes proofLEZeroN
    SS -> caseSnm
  where
    caseSnm :: forall n' m'. (SNatI n', SNatI m') => Dec (LEProof ('S n') m')
    caseSnm = case snat :: SNat m' of
        SZ -> No $ \p -> case p of {} -- ooh, GHC is smart!
        SS -> case decideLEProof of
            Yes p -> Yes (proofLESucc p)
            No  p -> No $ \p' -> p (proofLESucc' p')
-}
