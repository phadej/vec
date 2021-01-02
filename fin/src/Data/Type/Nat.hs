{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE EmptyCase            #-}
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
    snat,
    withSNat,
    reify,
    reflect,
    reflectToNum,
    -- * Equality
    eqNat,
    EqNat,
    discreteNat,
    -- * Induction
    induction1,
    -- ** Example: unfoldedFix
    unfoldedFix,
    -- * Arithmetic
    Plus,
    Mult,
    Mult2,
    DivMod2,
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

import Data.Function      (fix)
import Data.Proxy         (Proxy (..))
import Data.Type.Dec      (Dec (..))
import Data.Type.Equality ((:~:) (..), TestEquality (..))
import Data.Typeable      (Typeable)
import Numeric.Natural    (Natural)

import qualified GHC.TypeLits as GHC

import Unsafe.Coerce (unsafeCoerce)
import Data.Coerce (coerce)

#if !MIN_VERSION_base(4,11,0)
import Data.Type.Equality (type (==))
#endif

import Data.Nat

-- $setup
-- >>> :set -XTypeOperators -XDataKinds
-- >>> import Data.Type.Dec (decShow)

-------------------------------------------------------------------------------
-- SNat
-------------------------------------------------------------------------------

-- | Singleton of 'Nat'.
data SNat (n :: Nat) where
    SZ :: SNat 'Z
    SS :: SNatI n => SNat ('S n)
  deriving (Typeable)

deriving instance Show (SNat p)

-- | Implicit 'SNat'.
--
-- In an unorthodox singleton way, it actually provides an induction function.
--
-- The induction should often be fully inlined.
-- See @test/Inspection.hs@.
--
-- >>> :set -XPolyKinds
-- >>> newtype Const a b = Const a deriving (Show)
-- >>> induction (Const 0) (coerce ((+2) :: Int -> Int)) :: Const Int Nat3
-- Const 6
--
class SNatI (n :: Nat) where
    induction
        :: f 'Z                                    -- ^ zero case
        -> (forall m. SNatI m => f m -> f ('S m))  -- ^ induction step
        -> f n

instance SNatI 'Z where
    induction n _c = n

instance SNatI n => SNatI ('S n) where
    induction n c = c (induction n c)

-- | Construct explicit 'SNat' value.
snat :: SNatI n => SNat n
snat = induction SZ (\_ -> SS)

-- | Constructor 'SNatI' dictionary from 'SNat'.
--
-- @since 0.0.3
withSNat :: SNat n -> (SNatI n => r) -> r
withSNat SZ k = k
withSNat SS k = k

-- | Reflect type-level 'Nat' to the term level.
reflect :: forall n proxy. SNatI n => proxy n -> Nat
reflect _ = unKonst (induction (Konst Z) (kmap S) :: Konst Nat n)

-- | As 'reflect' but with any 'Num'.
reflectToNum :: forall n m proxy. (SNatI n, Num m) => proxy n -> m
reflectToNum _ = unKonst (induction (Konst 0) (kmap (1+)) :: Konst m n)

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
snatToNat SS = unKonst (induction (Konst Z) (kmap S) :: Konst Nat n)

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
snatToNatural SS = unKonst (induction (Konst 0) (kmap succ) :: Konst Natural n)

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

-- | Decide equality of type-level numbers.
--
-- >>> decShow (discreteNat :: Dec (Nat3 :~: Plus Nat1 Nat2))
-- "Yes Refl"
--
-- @since 0.0.3
discreteNat :: forall n m. (SNatI n, SNatI m) => Dec (n :~: m)
discreteNat = getDiscreteNat $ induction (DiscreteNat start) (\p -> DiscreteNat (step p))
  where
    start :: forall p. SNatI p => Dec ('Z :~: p)
    start = case snat :: SNat p of
        SZ -> Yes Refl
        SS -> No $ \p -> case p of {}

    step :: forall p q. SNatI q => DiscreteNat p -> Dec ('S p :~: q)
    step rec = case snat :: SNat q of
        SZ -> No $ \p -> case p of {}
        SS -> step' rec

    step' :: forall p q. SNatI q => DiscreteNat p -> Dec ('S p :~: 'S q)
    step' (DiscreteNat rec) = case rec :: Dec (p :~: q) of
        Yes Refl -> Yes Refl
        No np    -> No $ \Refl -> np Refl

newtype DiscreteNat n = DiscreteNat { getDiscreteNat :: forall m. SNatI m => Dec (n :~: m) }

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

#if !MIN_VERSION_base(4,11,0)
type instance n == m = EqNat n m
#endif

-------------------------------------------------------------------------------
-- Induction
-------------------------------------------------------------------------------

newtype Konst a (n :: Nat) = Konst { unKonst :: a }

kmap :: (a -> b) -> Konst a n -> Konst b m
kmap = coerce

newtype Flipped f a (b :: Nat) = Flip { unflip :: f b a }

-- | Induction on 'Nat', functor form. Useful for computation.
--
induction1
    :: forall n f a. SNatI n
    => f 'Z a                                      -- ^ zero case
    -> (forall m. SNatI m => f m a -> f ('S m) a)  -- ^ induction step
    -> f n a
induction1 z f = unflip (induction (Flip z) (\(Flip x) -> Flip (f x)))
{-# INLINE induction1 #-}

-- | Unfold @n@ steps of a general recursion.
--
-- /Note:/ Always __benchmark__. This function may give you both /bad/ properties:
-- a lot of code (increased binary size), and worse performance.
--
-- For known @n@ 'unfoldedFix' will unfold recursion, for example
--
-- @
-- 'unfoldedFix' ('Proxy' :: 'Proxy' 'Nat3') f = f (f (f (fix f)))
-- @
--
unfoldedFix :: forall n a proxy. SNatI n => proxy n -> (a -> a) -> a
unfoldedFix _ = getFix (induction start step :: Fix a n) where
    start :: Fix a 'Z
    start = Fix fix

    step :: Fix a m -> Fix a ('S m)
    step (Fix go) = Fix $ \f -> f (go f)

newtype Fix a (n :: Nat) = Fix { getFix :: (a -> a) -> a }

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

-- | Multiplication by two. Doubling.
--
-- >>> reflect (snat :: SNat (Mult2 Nat4))
-- 8
--
type family Mult2 (n :: Nat) :: Nat where
    Mult2 'Z     = 'Z
    Mult2 ('S n) = 'S ('S (Mult2 n))

-- | Division by two. 'False' is 0 and 'True' is 1 as a remainder.
--
-- >>> :kind! DivMod2 Nat7
-- DivMod2 Nat7 :: (Nat, Bool)
-- = '( 'S ('S ('S 'Z)), 'True)
--
-- >>> :kind! DivMod2 Nat4
-- DivMod2 Nat4 :: (Nat, Bool)
-- = '( 'S ('S 'Z), 'False)
--
type family DivMod2 (n :: Nat) :: (Nat, Bool) where
    DivMod2 'Z          = '( 'Z, 'False)
    DivMod2 ('S 'Z)     = '( 'Z, 'True)
    DivMod2 ('S ('S n)) = DivMod2' (DivMod2 n)

type family DivMod2' (p :: (Nat, Bool)) :: (Nat, Bool) where
    DivMod2' '(n, b) = '( 'S n, b)

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

-- | @n * 0 = 0@
proofMultNZero :: forall n proxy. SNatI n => proxy n -> Mult n Nat0 :~: Nat0
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
