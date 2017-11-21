{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- | 'Nat' numbers. @DataKinds@ stuff.
--
-- This module re-exports "Data.Nat", and adds type-level things.
module Data.Type.Nat (
    -- * Natural, Nat numbers
    Nat(..),
    toNatural,
    fromNatural,
    cata,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Singleton
    SNat(..),
    snatToNat,
    snatToNatural,
    -- * Implicit
    SNatI(..),
    reify,
    reflect,
    reflectToNum,
    -- * Equality
    eqNat,
    EqNat,
    -- * Induction
    induction,
    induction1,
    InlineInduction (..),
    inlineInduction,
    -- * Arithmetic
    Plus,
    Mult,
    -- * Conversion to GHC Nat
    ToGHC,
    FromGHC,
    -- * Aliases
    -- ** Nat
    nat0, nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9,
    -- ** promoted Nat
    Nat0, Nat1, Nat2, Nat3, Nat4, Nat5, Nat6, Nat7, Nat8, Nat9,
    -- * Proofs
    proofPlusZeroN,
    proofPlusNZero,
    proofMultZeroN,
    proofMultNZero,
    proofMultOneN,
    proofMultNOne,
    )  where

import Data.Nat
import Data.Proxy         (Proxy (..))
import Data.Type.Equality
import Numeric.Natural    (Natural)

import qualified GHC.TypeLits as GHC

import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- SNat
-------------------------------------------------------------------------------

-- | Singleton of 'Nat'.
data SNat (n :: Nat) where
    SZ :: SNat 'Z
    SS :: SNatI n => SNat ('S n)

deriving instance Show (SNat p)

-- | Convenience class to get 'SNat'.
class               SNatI (n :: Nat) where snat :: SNat n
instance            SNatI 'Z         where snat = SZ
instance SNatI n => SNatI ('S n)     where snat = SS

-- | Reflect type-level 'Nat' to the term level.
reflect :: forall n proxy. SNatI n => proxy n -> Nat
reflect _ = unTagged (induction1 (Tagged Z) (retagMap S) :: Tagged n Nat)

-- | As 'reflect' but with any 'Num'.
reflectToNum :: forall n m proxy. (SNatI n, Num m) => proxy n -> m
reflectToNum _ = unTagged (induction1 (Tagged 0) (retagMap (1+)) :: Tagged n m)

-- | Reify 'Nat'.
--
-- >>> reify nat3 reflect
-- 3
reify :: forall r. Nat -> (forall n. SNatI n => Proxy n -> r) -> r
reify Z     f = f (Proxy :: Proxy 'Z)
reify (S n) f =  reify n (\(_p :: Proxy n) -> f (Proxy :: Proxy ('S n)))

-- | Convert 'SNat' to 'Nat'.
--
-- >>> snatToNat (snat :: SNat Nat1)
-- 1
--
snatToNat :: forall n. SNat n -> Nat
snatToNat SZ = Z
snatToNat SS = unTagged (induction1 (Tagged Z) (retagMap S) :: Tagged n Nat)

-- | Convert 'SNat' to 'Natural'
--
-- >>> snatToNatural (snat :: SNat Nat0)
-- 0
--
-- >>> snatToNatural (snat :: SNat Nat2)
-- 2
--
snatToNatural :: forall n. SNat n -> Natural
snatToNatural SZ = 0
snatToNatural SS = unTagged (induction1 (Tagged 0) (retagMap succ) :: Tagged n Natural)

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

-- | Decide equality of type-level numbers.
--
-- >>> eqNat :: Maybe (Nat3 :~: Plus Nat1 Nat2)
-- Just Refl
--
-- >>> eqNat :: Maybe (Nat3 :~: Mult Nat2 Nat2)
-- Nothing
--
eqNat :: forall n m. (SNatI n, SNatI m) => Maybe (n :~: m)
eqNat = getNatEq $ induction (NatEq start) (\p -> NatEq (step p)) where
    start :: forall p. SNatI p => Maybe ('Z :~: p)
    start = case snat :: SNat p of
        SZ -> Just Refl
        SS -> Nothing

    step :: forall p q. SNatI q => NatEq p -> Maybe ('S p :~: q)
    step hind = case snat :: SNat q of
        SZ -> Nothing
        SS -> step' hind

    step' :: forall p q. SNatI q => NatEq p -> Maybe ('S p :~: 'S q)
    step' (NatEq hind) = do
        Refl <- hind :: Maybe (p :~: q)
        return Refl

newtype NatEq n = NatEq { getNatEq :: forall m. SNatI m => Maybe (n :~: m) }

instance TestEquality SNat where
    testEquality SZ SZ = Just Refl
    testEquality SZ SS = Nothing
    testEquality SS SZ = Nothing
    testEquality SS SS = eqNat

-- | Type family used to implement 'Data.Type.Equality.==' from "Data.Type.Equality" module.
type family EqNat (n :: Nat) (m :: Nat) where
    EqNat 'Z     'Z     = 'True
    EqNat ('S n) ('S m) = EqNat n m
    EqNat n      m      = 'False

type instance n == m = EqNat n m

-------------------------------------------------------------------------------
-- Induction
-------------------------------------------------------------------------------

-- | Induction on 'Nat', functor form. Useful for computation.
--
-- >>> induction1 (Tagged 0) $ retagMap (+2) :: Tagged Nat3 Int
-- Tagged 6
--
induction1
    :: forall n f a. SNatI n
    => f 'Z a                                      -- ^ zero case
    -> (forall m. SNatI m => f m a -> f ('S m) a)  -- ^ induction step
    -> f n a
induction1 z f = go where
    go :: forall m. SNatI m => f m a
    go = case snat :: SNat m of
        SZ -> z
        SS -> f go

-- | Induction on 'Nat'.
--
-- Useful in proofs or with GADTs, see source of 'proofPlusNZero'.
induction
    :: forall n f. SNatI n
    => f 'Z                                    -- ^ zero case
    -> (forall m. SNatI m => f m -> f ('S m))  -- ^ induction step
    -> f n
induction z f = go where
    go :: forall m. SNatI m => f m
    go = case snat :: SNat m of
        SZ -> z
        SS -> f go

-- | The induction will be fully inlined.
--
-- See @test/Inspection.hs@.
class SNatI n => InlineInduction (n :: Nat) where
    inlineInduction1 :: f 'Z a -> (forall m. InlineInduction m => f m a -> f ('S m) a) -> f n a

instance InlineInduction 'Z where
    inlineInduction1 z _ = z

instance InlineInduction n => InlineInduction ('S n) where
    inlineInduction1 z f = f (inlineInduction1 z f)

    -- Specialise this to few first numerals.
    {-# SPECIALIZE instance InlineInduction ('S 'Z) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S 'Z)) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S 'Z))) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S ('S 'Z)))) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S ('S ('S 'Z))))) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S ('S ('S ('S 'Z)))))) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S ('S ('S ('S ('S 'Z))))))) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S ('S ('S ('S ('S ('S 'Z)))))))) #-}
    {-# SPECIALIZE instance InlineInduction ('S ('S ('S ('S ('S ('S ('S ('S ('S 'Z))))))))) #-}

-- | See 'InlineInduction'.
inlineInduction
    :: forall n f. InlineInduction n
    => f 'Z                                              -- ^ zero case
    -> (forall m. InlineInduction m => f m -> f ('S m))  -- ^ induction step
    -> f n
inlineInduction z f = unConst' $ inlineInduction1 (Const' z) (Const' . f . unConst')

newtype Const' (f :: Nat -> *) (n :: Nat) a = Const' { unConst' :: f n }

-------------------------------------------------------------------------------
-- Conversion to GHC Nat
-------------------------------------------------------------------------------

-- | Convert to GHC 'GHC.Nat'.
--
-- >>> :kind! ToGHC Nat5
-- ToGHC Nat5 :: GHC.Nat
-- = 5
--
type family ToGHC (n :: Nat) :: GHC.Nat where
    ToGHC 'Z     = 0
    ToGHC ('S n) = 1 GHC.+ ToGHC n

-- | Convert from GHC 'GHC.Nat'.
--
-- >>> :kind! FromGHC 7
-- FromGHC 7 :: Nat
-- = 'S ('S ('S ('S ('S ('S ('S 'Z))))))
--
type family FromGHC (n :: GHC.Nat) :: Nat where
    FromGHC 0 = 'Z
    FromGHC n = 'S (FromGHC (n GHC.- 1))

-------------------------------------------------------------------------------
-- Arithmetic
-------------------------------------------------------------------------------

-- | Addition.
--
-- >>> reflect (snat :: SNat (Plus Nat1 Nat2))
-- 3
type family Plus (n :: Nat) (m :: Nat) :: Nat where
    Plus 'Z     m = m
    Plus ('S n) m = 'S (Plus n m)

-- | Multiplication.
--
-- >>> reflect (snat :: SNat (Mult Nat2 Nat3))
-- 6
type family Mult (n :: Nat) (m :: Nat) :: Nat where
    Mult 'Z     m = 'Z
    Mult ('S n) m = Plus m (Mult n m)

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

type Nat0  = 'Z
type Nat1  = 'S Nat0
type Nat2  = 'S Nat1
type Nat3  = 'S Nat2
type Nat4  = 'S Nat3
type Nat5  = 'S Nat4
type Nat6  = 'S Nat5
type Nat7  = 'S Nat6
type Nat8  = 'S Nat7
type Nat9  = 'S Nat8

-------------------------------------------------------------------------------
-- proofs
-------------------------------------------------------------------------------

-- | @0 + n = n@
proofPlusZeroN :: Plus Nat0 n :~: n
proofPlusZeroN = Refl

-- | @n + 0 = n@
proofPlusNZero :: SNatI n => Plus n Nat0 :~: n
proofPlusNZero = getProofPlusNZero $ induction (ProofPlusNZero Refl) step where
    step :: forall m. ProofPlusNZero m -> ProofPlusNZero ('S m)
    step (ProofPlusNZero Refl) = ProofPlusNZero Refl

{-# NOINLINE [1] proofPlusNZero #-}
{-# RULES "Nat: n + 0 = n" proofPlusNZero = unsafeCoerce (Refl :: () :~: ()) #-}

newtype ProofPlusNZero n = ProofPlusNZero { getProofPlusNZero :: Plus n Nat0 :~: n }

-- TODO: plusAssoc

-- | @0 * n = 0@
proofMultZeroN :: Mult Nat0 n :~: Nat0
proofMultZeroN = Refl

-- | @n * 0 = n@
proofMultNZero :: forall n. SNatI n => Proxy n -> Mult n Nat0 :~: Nat0
proofMultNZero _ =
    getProofMultNZero (induction (ProofMultNZero Refl) step :: ProofMultNZero n)
  where
    step :: forall m. ProofMultNZero m -> ProofMultNZero ('S m)
    step (ProofMultNZero Refl) = ProofMultNZero Refl

{-# NOINLINE [1] proofMultNZero #-}
{-# RULES "Nat: n * 0 = n" proofMultNZero = unsafeCoerce (Refl :: () :~: ()) #-}

newtype ProofMultNZero n = ProofMultNZero { getProofMultNZero :: Mult n Nat0 :~: Nat0 }

-- | @1 * n = n@
proofMultOneN :: SNatI n => Mult Nat1 n :~: n
proofMultOneN = proofPlusNZero

{-# NOINLINE [1] proofMultOneN #-}
{-# RULES "Nat: 1 * n = n" proofMultOneN = unsafeCoerce (Refl :: () :~: ()) #-}

-- | @n * 1 = n@
proofMultNOne :: SNatI n => Mult n Nat1 :~: n
proofMultNOne = getProofMultNOne $ induction (ProofMultNOne Refl) step where
    step :: forall m. ProofMultNOne m -> ProofMultNOne ('S m)
    step (ProofMultNOne Refl) = ProofMultNOne Refl

{-# NOINLINE [1] proofMultNOne #-}
{-# RULES "Nat: n * 1 = n" proofMultNOne = unsafeCoerce (Refl :: () :~: ()) #-}

newtype ProofMultNOne n = ProofMultNOne { getProofMultNOne :: Mult n Nat1 :~: n }

-- TODO: multAssoc

-------------------------------------------------------------------------------
-- Tagged
-------------------------------------------------------------------------------

-- Own 'Tagged', to not depend on @tagged@
--
-- We shouldn't export this in public interface.
newtype Tagged (n :: Nat) a = Tagged a deriving Show

unTagged :: Tagged n a -> a
unTagged (Tagged a) = a

retagMap :: (a -> b) -> Tagged n a -> Tagged m b
retagMap f = Tagged . f . unTagged

-- $setup
-- >>> :set -XTypeOperators -XDataKinds
