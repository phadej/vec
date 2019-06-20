{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE UndecidableInstances  #-}
module Data.Type.Nat.LE.ReflStep (
    -- * Relation
    LEProof (..),
    fromZeroSucc,
    toZeroSucc,
    -- * Decidability
    decideLE,
    -- * Lemmas
    -- ** Constructor like
    leZero,
    leSucc,
    leRefl,
    leStep,
    -- ** Partial order
    leAsym,
    leTrans,
    -- ** Total order
    leSwap,
    leSwap',
    -- ** More
    leStepL,
    lePred,
    proofZeroLEZero,
    ) where

import Data.Type.Dec      (Dec (..), Decidable (..), Neg)
import Data.Type.Equality
import Data.Type.Nat
import Data.Void          (absurd)

import qualified Data.Type.Nat.LE as ZeroSucc

-------------------------------------------------------------------------------
-- Proof
-------------------------------------------------------------------------------

-- | An evidence of \(n \le m\). /refl+step/ definition.
data LEProof n m where
    LERefl :: LEProof n n
    LEStep :: LEProof n m -> LEProof n ('S m)

deriving instance Show (LEProof n m)

-- | 'LEProof' values are unique (not @'Boring'@ though!).
instance Eq (LEProof n m) where
    _ == _ = True

instance Ord (LEProof n m) where
    compare _ _ = EQ

-------------------------------------------------------------------------------
-- Conversion
-------------------------------------------------------------------------------

-- | Convert from /zero+succ/ to /refl+step/ definition.
--
-- Inverse of 'toZeroSucc'.
--
fromZeroSucc :: forall n m. SNatI m => ZeroSucc.LEProof n m -> LEProof n m
fromZeroSucc ZeroSucc.LEZero     = leZero
fromZeroSucc (ZeroSucc.LESucc p) = case snat :: SNat m of
    SS -> leSucc (fromZeroSucc p)
    -- q  -> case q of {} -- for older GHC

-- | Convert /refl+step/ to /zero+succ/ definition.
--
-- Inverse of 'fromZeroSucc'.
--
toZeroSucc :: SNatI n => LEProof n m -> ZeroSucc.LEProof n m
toZeroSucc LERefl     = ZeroSucc.leRefl
toZeroSucc (LEStep p) = ZeroSucc.leStep (toZeroSucc p)

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | \(\forall n : \mathbb{N}, 0 \le n \)
leZero :: forall n. SNatI n => LEProof 'Z n
leZero = case snat :: SNat n of
    SZ -> LERefl
    SS -> LEStep leZero

-- | \(\forall n\, m : \mathbb{N}, n \le m \to 1 + n \le 1 + m \)
leSucc :: LEProof n m -> LEProof ('S n) ('S m)
leSucc LERefl     = LERefl
leSucc (LEStep p) = LEStep (leSucc p)

-- | \(\forall n\, m : \mathbb{N}, 1 + n \le 1 + m \to n \le m \)
lePred :: LEProof ('S n) ('S m) -> LEProof n m
lePred LERefl              = LERefl
lePred (LEStep LERefl)     = LEStep LERefl
lePred (LEStep (LEStep q)) = LEStep (leStepL q)

-- | \(\forall n : \mathbb{N}, n \le n \)
leRefl :: LEProof n n
leRefl = LERefl

-- | \(\forall n\, m : \mathbb{N}, n \le m \to n \le 1 + m \)
leStep :: LEProof n m -> LEProof n ('S m)
leStep = LEStep

-- | \(\forall n\, m : \mathbb{N}, 1 + n \le m \to n \le m \)
leStepL :: LEProof ('S n) m -> LEProof n m
leStepL LERefl     = LEStep LERefl
leStepL (LEStep p) = LEStep (leStepL p)

-- | \(\forall n\, m : \mathbb{N}, n \le m \to m \le n \to n \equiv m \)
leAsym :: LEProof n m -> LEProof m n -> n :~: m
leAsym LERefl _ = Refl
leAsym _ LERefl = Refl
leAsym (LEStep p) (LEStep q) = case leAsym (leStepL p) (leStepL q) of
    Refl -> Refl

-- | \(\forall n\, m\, p : \mathbb{N}, n \le m \to m \le p \to n \le p \)
leTrans :: LEProof n m -> LEProof m p -> LEProof n p
leTrans p LERefl     = p
leTrans p (LEStep q) = LEStep $ leTrans p q

-- | \(\forall n\, m : \mathbb{N}, \neg (n \le m) \to 1 + m \le n \)
leSwap :: forall n m. (SNatI n, SNatI m) => Neg (LEProof n m) -> LEProof ('S m) n
leSwap np = case (snat :: SNat m, snat :: SNat n) of
    (_,  SZ) -> absurd (np leZero)
    (SZ, SS) -> leSucc leZero
    (SS, SS) -> leSucc $ leSwap $ \p -> np $ leSucc p

-- | \(\forall n\, m : \mathbb{N}, n \le m \to \neg (1 + m \le n) \)
leSwap' :: LEProof n m -> LEProof ('S m) n -> void
leSwap' p LERefl     = case p of LEStep p' -> leSwap' (leStepL p') LERefl
leSwap' p (LEStep q) = leSwap' (leStepL p) q

-------------------------------------------------------------------------------
-- Decidability
-------------------------------------------------------------------------------

-- | Find the @'LEProof' n m@, i.e. compare numbers.
decideLE :: forall n m. (SNatI n, SNatI m) => Dec (LEProof n m)
decideLE = case snat :: SNat n of
    SZ -> Yes leZero
    SS -> caseSnm
  where
    caseSnm :: forall n' m'. (SNatI n', SNatI m') => Dec (LEProof ('S n') m')
    caseSnm = case snat :: SNat m' of
        SZ -> No $ \p -> case p of {} -- ooh, GHC is smart!
        SS -> case decideLE of
            Yes p -> Yes (leSucc p)
            No  p -> No $ \p' -> p (lePred p')

instance (SNatI n, SNatI m) => Decidable (LEProof n m) where
    decide = decideLE

-------------------------------------------------------------------------------
-- More lemmas
---------------------------------------------------------------------------------

-- | \(\forall n\ : \mathbb{N}, n \le 0 \to n \equiv 0 \)
proofZeroLEZero :: LEProof n 'Z -> n :~: 'Z
proofZeroLEZero LERefl = Refl
