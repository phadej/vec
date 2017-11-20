{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Finite numbers.
--
-- This module is designed to be imported qualified.
module Data.Fin (
    Fin (..),
    cata,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Conversions
    toNat,
    fromNat,
    toNatural,
    toInteger,
    -- * Interesting
    inverse,
    universe,
    inlineUniverse,
    universe1,
    inlineUniverse1,
    absurd,
    boring,
    -- * Aliases
    zeroth, first, second, third, fourth, fifth, sixth, seventh, eighth, ninth,
    ) where

import Control.DeepSeq    (NFData (..))
import Data.Hashable      (Hashable (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy         (Proxy (..))
import Data.Typeable      (Typeable)
import GHC.Exception      (ArithException (..), throw)
import Numeric.Natural    (Natural)

import qualified Data.List.NonEmpty as NE
import qualified Data.Type.Nat      as N

-- | Finite Numbers up to 'n'.
data Fin (n :: N.Nat) where
    Z :: Fin ('N.S n)
    S :: Fin n -> Fin ('N.S n)
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

-- | 'Fin' is printed as 'Natural'.
--
-- To see explicit structure, use 'explicitShow' or 'explicitShowsPrec'
instance Show (Fin n) where
    showsPrec d  = showsPrec d . toNatural

-- | Operations module @n@.
--
-- >>> map fromInteger [0, 1, 2, 3, 4, -5] :: [Fin N.Three]
-- [0,1,2,0,1,1]
--
-- >>> fromInteger 42 :: Fin N.Zero
-- *** Exception: divide by zero
-- ...
--
-- >>> signum (Z :: Fin N.One)
-- *** Exception: signum @(Fin n): not implemented
-- ...
--
-- >>> 2 + 3 :: Fin N.Four
-- 1
--
-- >>> 2 * 3 :: Fin N.Four
-- 2
--
instance N.SNatI n => Num (Fin n) where
    abs = id
    signum = error "signum @(Fin n): not implemented"

    fromInteger = unsafeFromNum . (`mod` (N.reflectToNum (Proxy :: Proxy n)))

    n + m = fromInteger (toInteger n + toInteger m)
    n * m = fromInteger (toInteger n * toInteger m)
    n - m = fromInteger (toInteger n - toInteger m)

    negate = fromInteger . negate . toInteger

instance N.SNatI n => Real (Fin n) where
    toRational = cata 0 succ

-- | 'quot' works only on @'Fin' n@ where @n@ is prime.
instance N.SNatI n => Integral (Fin n) where
    toInteger = cata 0 succ

    quotRem a b = (quot a b, 0)
    quot a b = a * inverse b

-- | Multiplicative inverse.
--
-- Works for @'Fin' n@ where @n@ is coprime with an argument, i.e. in general when @n@ is prime.
--
-- >>> map inverse universe :: [Fin N.Five]
-- [0,1,3,2,4]
--
-- >>> zipWith (*) universe (map inverse universe) :: [Fin N.Five]
-- [0,1,1,1,1]
--
-- Adaptation of [pseudo-code in Wikipedia](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm#Modular_integers)
--
inverse :: forall n. N.SNatI n => Fin n -> Fin n
inverse = fromInteger . iter 0 n 1 . toInteger where
    n = N.reflectToNum (Proxy :: Proxy n)

    iter t _ _  0
        | t < 0     = t + n
        | otherwise = t
    iter t r t' r' =
        let q = r `div` r'
        in iter t' r' (t - q * t') (r - q * r')

instance N.SNatI n => Enum (Fin n) where
    fromEnum = go where
        go :: Fin m -> Int
        go Z     = 0
        go (S n) = succ (go n)

    toEnum = unsafeFromNum

instance (n ~ 'N.S m, N.SNatI m) => Bounded (Fin n) where
    minBound = Z
    maxBound = getMaxBound $ N.induction
        (MaxBound Z)
        (MaxBound . S . getMaxBound)

newtype MaxBound n = MaxBound { getMaxBound :: Fin ('N.S n) }

instance NFData (Fin n) where
    rnf Z     = ()
    rnf (S n) = rnf n

instance Hashable (Fin n) where
    hashWithSalt salt = hashWithSalt salt . cata (0 :: Integer) succ

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'Fin'.
--
-- >>> explicitShow (0 :: Fin N.One)
-- "Z"
--
-- >>> explicitShow (2 :: Fin N.Three)
-- "S (S Z)"
--
explicitShow :: Fin n -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'showsPrec' displaying a structure of 'Fin'.
explicitShowsPrec :: Int -> Fin n -> ShowS
explicitShowsPrec _ Z     = showString "Z"
explicitShowsPrec d (S n) = showParen (d > 10)
    $ showString "S "
    . explicitShowsPrec 11 n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Fold 'Fin'.
cata :: forall a n. a -> (a -> a) -> Fin n -> a
cata z f = go where
    go :: Fin m -> a
    go Z = z
    go (S n) = f (go n)

-- | Convert to 'Nat'.
toNat :: Fin n -> N.Nat
toNat = cata N.Z N.S

-- | Convert from 'Nat'.
--
-- >>> fromNat N.one :: Maybe (Fin N.Two)
-- Just 1
--
-- >>> fromNat N.one :: Maybe (Fin N.One)
-- Nothing
--
fromNat :: N.SNatI n => N.Nat -> Maybe (Fin n)
fromNat = appNatToFin (N.induction start step) where
    start :: NatToFin 'N.Z
    start = NatToFin $ const Nothing

    step :: NatToFin n -> NatToFin ('N.S n)
    step (NatToFin f) = NatToFin $ \n -> case n of
        N.Z   -> Just Z
        N.S m -> fmap S (f m)

newtype NatToFin n = NatToFin { appNatToFin :: N.Nat -> Maybe (Fin n) }

-- | Convert to 'Natural'.
toNatural :: Fin n -> Natural
toNatural = cata 0 succ

-- | Convert from any 'Ord' 'Num'.
unsafeFromNum :: forall n i. (Num i, Ord i, N.SNatI n) => i -> Fin n
unsafeFromNum = appUnsafeFromNum (N.induction start step) where
    start :: UnsafeFromNum i 'N.Z
    start = UnsafeFromNum $ \n -> case compare n 0 of
        LT -> throw Underflow
        EQ -> throw Overflow
        GT -> throw Overflow

    step :: UnsafeFromNum i m -> UnsafeFromNum i ('N.S m)
    step (UnsafeFromNum f) = UnsafeFromNum $ \n -> case compare n 0 of
        EQ -> Z
        GT -> S (f (n - 1))
        LT -> throw Underflow

newtype UnsafeFromNum i n = UnsafeFromNum { appUnsafeFromNum :: i -> Fin n }

-------------------------------------------------------------------------------
-- "Interesting" stuff
-------------------------------------------------------------------------------

-- | All values. @[minBound .. maxBound]@ won't work for @'Fin' 'N.Zero'@.
--
-- >>> universe :: [Fin N.Three]
-- [0,1,2]
universe :: N.SNatI n => [Fin n]
universe = getUniverse $ N.induction (Universe []) step where
    step :: Universe n -> Universe ('N.S n)
    step (Universe xs) = Universe (Z : map S xs)

-- | Like 'universe' but 'NonEmpty'.
--
-- >>> universe1 :: NonEmpty (Fin N.Three)
-- 0 :| [1,2]
universe1 :: N.SNatI n => NonEmpty (Fin ('N.S n))
universe1 = getUniverse1 $ N.induction (Universe1 (Z :| [])) step where
    step :: Universe1 n -> Universe1 ('N.S n)
    step (Universe1 xs) = Universe1 (NE.cons Z (fmap S xs))

-- | 'universe' which will be fully inlined, if @n@ is known at compile time.
--
-- >>> inlineUniverse :: [Fin N.Three]
-- [0,1,2]
inlineUniverse :: N.InlineInduction n => [Fin n]
inlineUniverse = getUniverse $ N.inlineInduction (Universe []) step where
    step :: Universe n -> Universe ('N.S n)
    step (Universe xs) = Universe (Z : map S xs)

-- | >>> inlineUniverse1 :: NonEmpty (Fin N.Three)
-- 0 :| [1,2]
inlineUniverse1 :: N.InlineInduction n => NonEmpty (Fin ('N.S n))
inlineUniverse1 = getUniverse1 $ N.inlineInduction (Universe1 (Z :| [])) step where
    step :: Universe1 n -> Universe1 ('N.S n)
    step (Universe1 xs) = Universe1 (NE.cons Z (fmap S xs))

newtype Universe  n = Universe  { getUniverse  :: [Fin n] }
newtype Universe1 n = Universe1 { getUniverse1 :: NonEmpty (Fin ('N.S n)) }

-- | @'Fin' 'N.Zero'@ is inhabited.
absurd :: Fin N.Zero -> b
absurd n = case n of {}

-- | Counting to one is boring.
--
-- >>> boring
-- 0
boring :: Fin N.One
boring = Z

{-
import Data.Boring (Boring (..), Absurd (..))

instance z ~ N.Zero => Absurd (Fin z) where
    absurd n = case n of {}

instance one ~ N.One => Boring (Fin z) where
    boring = Z
-}

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

-- | We start counting from zero.
zeroth  :: Fin (N.Plus N.Zero  ('N.S n))

first   :: Fin (N.Plus N.One   ('N.S n))
second  :: Fin (N.Plus N.Two   ('N.S n))
third   :: Fin (N.Plus N.Three ('N.S n))
fourth  :: Fin (N.Plus N.Four  ('N.S n))
fifth   :: Fin (N.Plus N.Five  ('N.S n))
sixth   :: Fin (N.Plus N.Six   ('N.S n))
seventh :: Fin (N.Plus N.Seven ('N.S n))
eighth  :: Fin (N.Plus N.Eight ('N.S n))
ninth   :: Fin (N.Plus N.Nine  ('N.S n))

zeroth  = Z
first   = S zeroth
second  = S first
third   = S second
fourth  = S third
fifth   = S fourth
sixth   = S fifth
seventh = S sixth
eighth  = S seventh
ninth   = S eighth
