{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE UndecidableInstances  #-}
-- | Less-than-or-equal relation for (unary) natural numbers 'Nat'.
--
-- There are at least three ways to encode this relation.
--
-- * \(zero : 0 \le m\) and \(succ : n \le m \to 1 + n \le 1 + m\) (this module),
--
-- * \(refl : n \le n \) and \(step : n \le m \to n \le 1 + m\) ("Data.Type.Nat.LE.ReflStep"),
--
-- * \(ex : \exists p. n + p \equiv m \) (tricky in Haskell).
--
-- Depending on a situation, usage ergonomics are different.
--
module Data.Type.Nat.LE (
    -- * Relation
    LE (..),
    LEProof (..),
    withLEProof,
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

-------------------------------------------------------------------------------
-- Proof
-------------------------------------------------------------------------------

-- | An evidence of \(n \le m\). /zero+succ/ definition.
data LEProof n m where
    LEZero :: LEProof 'Z m
    LESucc :: LEProof n m -> LEProof ('S n) ('S m)

deriving instance Show (LEProof n m)

-- | 'LEProof' values are unique (not @'Boring'@ though!).
instance Eq (LEProof n m) where
    _ == _ = True

instance Ord (LEProof n m) where
    compare _ _ = EQ

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Total order of 'Nat', less-than-or-Equal-to, \( \le \).
--
class LE n m where
    leProof :: LEProof n m

instance LE 'Z m where
    leProof = LEZero

instance (m ~ 'S m', LE n m') => LE ('S n) m where
    leProof = LESucc leProof

-- | Constructor 'LE' dictionary from 'LEProof'.
withLEProof :: LEProof n m -> (LE n m => r) -> r
withLEProof LEZero     k = k
withLEProof (LESucc p) k = withLEProof p k

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | \(\forall n : \mathbb{N}, 0 \le n \)
leZero :: LEProof 'Z n
leZero = LEZero

-- | \(\forall n\, m : \mathbb{N}, n \le m \to 1 + n \le 1 + m \)
leSucc :: LEProof n m -> LEProof ('S n) ('S m)
leSucc = LESucc

-- | \(\forall n\, m : \mathbb{N}, 1 + n \le 1 + m \to n \le m \)
lePred :: LEProof ('S n) ('S m) -> LEProof n m
lePred (LESucc p) = p

-- | \(\forall n : \mathbb{N}, n \le n \)
leRefl :: forall n. SNatI n => LEProof n n
leRefl = case snat :: SNat n of
    SZ -> LEZero
    SS -> LESucc leRefl

-- | \(\forall n\, m : \mathbb{N}, n \le m \to n \le 1 + m \)
leStep :: LEProof n m -> LEProof n ('S m)
leStep LEZero     = LEZero
leStep (LESucc p) = LESucc (leStep p)

-- | \(\forall n\, m : \mathbb{N}, 1 + n \le m \to n \le m \)
leStepL :: LEProof ('S n) m -> LEProof n m
leStepL (LESucc p) = leStep p

-- | \(\forall n\, m : \mathbb{N}, n \le m \to m \le n \to n \equiv m \)
leAsym :: LEProof n m -> LEProof m n -> n :~: m
leAsym LEZero     LEZero     = Refl
leAsym (LESucc p) (LESucc q) = case leAsym p q of Refl -> Refl
-- leAsym LEZero p = case p of {}
-- leAsym p LEZero = case p of {}

-- | \(\forall n\, m\, p : \mathbb{N}, n \le m \to m \le p \to n \le p \)
leTrans :: LEProof n m -> LEProof m p -> LEProof n p
leTrans LEZero     _          = LEZero
leTrans (LESucc p) (LESucc q) = LESucc (leTrans p q)
-- leTrans (LESucc _) q = case q of {}

-- | \(\forall n\, m : \mathbb{N}, \neg (n \le m) \to 1 + m \le n \)
leSwap :: forall n m. (SNatI n, SNatI m) => Neg (LEProof n m) -> LEProof ('S m) n
leSwap np = case (snat :: SNat m, snat :: SNat n) of
    (_,  SZ) -> absurd (np LEZero)
    (SZ, SS) -> LESucc LEZero
    (SS, SS) -> LESucc $ leSwap $ \p -> np $ LESucc p

-- | \(\forall n\, m : \mathbb{N}, n \le m \to \neg (1 + m \le n) \)
--
-- >>> leProof :: LEProof Nat2 Nat3
-- LESucc (LESucc LEZero)
--
-- >>> leSwap (leSwap' (leProof :: LEProof Nat2 Nat3))
-- LESucc (LESucc (LESucc LEZero))
--
-- >>> lePred (leSwap (leSwap' (leProof :: LEProof Nat2 Nat3)))
-- LESucc (LESucc LEZero)
--
leSwap' :: LEProof n m -> LEProof ('S m) n -> void
leSwap' p (LESucc q) = case p of LESucc p' -> leSwap' p' q

-------------------------------------------------------------------------------
-- Dedidablity
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
-------------------------------------------------------------------------------

-- | \(\forall n\ : \mathbb{N}, n \le 0 \to n \equiv 0 \)
proofZeroLEZero :: LEProof n 'Z -> n :~: 'Z
proofZeroLEZero LEZero = Refl
