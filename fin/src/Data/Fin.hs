{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Safe                 #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Finite numbers.
--
-- This module is designed to be imported as
--
-- @
-- import Data.Fin (Fin (..))
-- import qualified Data.Fin as Fin
-- @
--
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
    mirror,
    inverse,
    universe,
    inlineUniverse,
    universe1,
    inlineUniverse1,
    absurd,
    boring,
    -- * Plus
    weakenLeft,
    weakenLeft1,
    weakenRight,
    weakenRight1,
    append,
    split,
    -- * Min and max
    isMin,
    isMax,
    -- * Aliases
    fin0, fin1, fin2, fin3, fin4, fin5, fin6, fin7, fin8, fin9,
    ) where

import Control.DeepSeq    (NFData (..))
import Data.Bifunctor     (bimap)
import Data.Hashable      (Hashable (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy         (Proxy (..))
import Data.Type.Nat      (Nat (..))
import Data.Typeable      (Typeable)
import GHC.Exception      (ArithException (..), throw)
import Numeric.Natural    (Natural)

import qualified Data.Boring           as Boring
import qualified Data.List.NonEmpty    as NE
import qualified Data.Type.Nat         as N
import qualified Data.Universe.Class   as U
import qualified Data.Universe.Helpers as U
import qualified Test.QuickCheck       as QC

-- $setup
-- >>> import Data.List (genericLength)
-- >>> import Data.List.NonEmpty (NonEmpty (..))
-- >>> import Numeric.Natural (Natural)
-- >>> import qualified Data.Type.Nat as N
-- >>> import qualified Data.Universe.Class as U
-- >>> import qualified Data.Universe.Helpers as U

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

-- | Finite numbers: @[0..n-1]@.
data Fin (n :: Nat) where
    FZ :: Fin ('S n)
    FS :: Fin n -> Fin ('S n)
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
-- >>> map fromInteger [0, 1, 2, 3, 4, -5] :: [Fin N.Nat3]
-- [0,1,2,0,1,1]
--
-- >>> fromInteger 42 :: Fin N.Nat0
-- *** Exception: divide by zero
-- ...
--
-- >>> signum (FZ :: Fin N.Nat1)
-- 0
--
-- >>> signum (3 :: Fin N.Nat4)
-- 1
--
-- >>> 2 + 3 :: Fin N.Nat4
-- 1
--
-- >>> 2 * 3 :: Fin N.Nat4
-- 2
--
instance N.SNatI n => Num (Fin n) where
    abs = id

    signum FZ          = FZ
    signum (FS FZ)     = FS FZ
    signum (FS (FS _)) = FS FZ

    fromInteger = unsafeFromNum . (`mod` N.reflectToNum (Proxy :: Proxy n))

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

-- | Mirror the values, 'minBound' becomes 'maxBound', etc.
--
-- >>> map mirror universe :: [Fin N.Nat4]
-- [3,2,1,0]
--
-- >>> reverse universe :: [Fin N.Nat4]
-- [3,2,1,0]
--
-- @since 0.1.1
--
mirror :: forall n. N.SNatI n => Fin n -> Fin n
mirror = getMirror (N.induction start step) where
    start :: Mirror 'Z
    start = Mirror id

    step :: forall m. N.SNatI m => Mirror m -> Mirror ('S m)
    step (Mirror rec) = Mirror $ \n -> case n of
        FZ   -> getMaxBound (N.induction (MaxBound FZ) (MaxBound . FS . getMaxBound))
        FS m -> weakenLeft1 (rec m)

newtype Mirror n = Mirror { getMirror :: Fin n -> Fin n }

-- | Multiplicative inverse.
--
-- Works for @'Fin' n@ where @n@ is coprime with an argument, i.e. in general when @n@ is prime.
--
-- >>> map inverse universe :: [Fin N.Nat5]
-- [0,1,3,2,4]
--
-- >>> zipWith (*) universe (map inverse universe) :: [Fin N.Nat5]
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
        go FZ     = 0
        go (FS n) = succ (go n)

    toEnum = unsafeFromNum

instance (n ~ 'S m, N.SNatI m) => Bounded (Fin n) where
    minBound = FZ
    maxBound = getMaxBound $ N.induction
        (MaxBound FZ)
        (MaxBound . FS . getMaxBound)

newtype MaxBound n = MaxBound { getMaxBound :: Fin ('S n) }

instance NFData (Fin n) where
    rnf FZ     = ()
    rnf (FS n) = rnf n

instance Hashable (Fin n) where
    hashWithSalt salt = hashWithSalt salt . cata (0 :: Integer) succ

-------------------------------------------------------------------------------
-- Boring
-------------------------------------------------------------------------------

-- | @since 0.2.1
instance n ~ 'Z => Boring.Absurd (Fin n) where
    absurd = absurd

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance (n ~ 'S m, N.SNatI m) => QC.Arbitrary (Fin n) where
    arbitrary = getArb $ N.induction (Arb (return FZ)) step where
        step :: forall p. N.SNatI p => Arb p -> Arb ('S p)
        step (Arb p) = Arb $ QC.frequency
            [ (1,                                 return FZ)
            , (N.reflectToNum (Proxy :: Proxy p), fmap FS p)
            ]

    shrink = shrink

shrink :: Fin n -> [Fin n]
shrink FZ      = []
shrink (FS FZ) = [FZ]
shrink (FS n)  = map FS (shrink n)

newtype Arb n = Arb { getArb :: QC.Gen (Fin ('S n)) }

instance QC.CoArbitrary (Fin n) where
    coarbitrary FZ     = QC.variant (0 :: Int)
    coarbitrary (FS n) = QC.variant (1 :: Int) . QC.coarbitrary n

instance (n ~ 'S m, N.SNatI m) => QC.Function (Fin n) where
    function = case N.snat :: N.SNat m of
        N.SZ -> QC.functionMap (\_ -> ()) (\() -> FZ)
        N.SS -> QC.functionMap isMin      (maybe FZ FS)

-- TODO: https://github.com/nick8325/quickcheck/pull/283
-- newtype Fun b m = Fun { getFun :: (Fin ('S m) -> b) -> Fin ('S m) QC.:-> b }

-------------------------------------------------------------------------------
-- universe-base
-------------------------------------------------------------------------------

-- | @since 0.1.2
instance N.SNatI n => U.Universe (Fin n) where
    universe = universe

-- |
--
-- >>> (U.cardinality :: U.Tagged (Fin N.Nat3) Natural) == U.Tagged (genericLength (U.universeF :: [Fin N.Nat3]))
-- True
--
-- @since 0.1.2
--
instance N.SNatI n => U.Finite   (Fin n) where
    universeF   = U.universe
    cardinality = U.Tagged $ N.reflectToNum (Proxy :: Proxy n)

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'Fin'.
--
-- >>> explicitShow (0 :: Fin N.Nat1)
-- "FZ"
--
-- >>> explicitShow (2 :: Fin N.Nat3)
-- "FS (FS FZ)"
--
explicitShow :: Fin n -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'showsPrec' displaying a structure of 'Fin'.
explicitShowsPrec :: Int -> Fin n -> ShowS
explicitShowsPrec _ FZ     = showString "FZ"
explicitShowsPrec d (FS n) = showParen (d > 10)
    $ showString "FS "
    . explicitShowsPrec 11 n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Fold 'Fin'.
cata :: forall a n. a -> (a -> a) -> Fin n -> a
cata z f = go where
    go :: Fin m -> a
    go FZ = z
    go (FS n) = f (go n)

-- | Convert to 'Nat'.
toNat :: Fin n -> N.Nat
toNat = cata Z S

-- | Convert from 'Nat'.
--
-- >>> fromNat N.nat1 :: Maybe (Fin N.Nat2)
-- Just 1
--
-- >>> fromNat N.nat1 :: Maybe (Fin N.Nat1)
-- Nothing
--
fromNat :: N.SNatI n => N.Nat -> Maybe (Fin n)
fromNat = appNatToFin (N.induction start step) where
    start :: NatToFin 'Z
    start = NatToFin $ const Nothing

    step :: NatToFin n -> NatToFin ('S n)
    step (NatToFin f) = NatToFin $ \n -> case n of
        Z   -> Just FZ
        S m -> fmap FS (f m)

newtype NatToFin n = NatToFin { appNatToFin :: N.Nat -> Maybe (Fin n) }

-- | Convert to 'Natural'.
toNatural :: Fin n -> Natural
toNatural = cata 0 succ

-- | Convert from any 'Ord' 'Num'.
unsafeFromNum :: forall n i. (Num i, Ord i, N.SNatI n) => i -> Fin n
unsafeFromNum = appUnsafeFromNum (N.induction start step) where
    start :: UnsafeFromNum i 'Z
    start = UnsafeFromNum $ \n -> case compare n 0 of
        LT -> throw Underflow
        EQ -> throw Overflow
        GT -> throw Overflow

    step :: UnsafeFromNum i m -> UnsafeFromNum i ('S m)
    step (UnsafeFromNum f) = UnsafeFromNum $ \n -> case compare n 0 of
        EQ -> FZ
        GT -> FS (f (n - 1))
        LT -> throw Underflow

newtype UnsafeFromNum i n = UnsafeFromNum { appUnsafeFromNum :: i -> Fin n }

-------------------------------------------------------------------------------
-- "Interesting" stuff
-------------------------------------------------------------------------------

-- | All values. @[minBound .. maxBound]@ won't work for @'Fin' 'N.Nat0'@.
--
-- >>> universe :: [Fin N.Nat3]
-- [0,1,2]
universe :: N.SNatI n => [Fin n]
universe = getUniverse $ N.induction (Universe []) step where
    step :: Universe n -> Universe ('S n)
    step (Universe xs) = Universe (FZ : map FS xs)

-- | Like 'universe' but 'NonEmpty'.
--
-- >>> universe1 :: NonEmpty (Fin N.Nat3)
-- 0 :| [1,2]
universe1 :: N.SNatI n => NonEmpty (Fin ('S n))
universe1 = getUniverse1 $ N.induction (Universe1 (FZ :| [])) step where
    step :: Universe1 n -> Universe1 ('S n)
    step (Universe1 xs) = Universe1 (NE.cons FZ (fmap FS xs))

-- | 'universe' which will be fully inlined, if @n@ is known at compile time.
--
-- >>> inlineUniverse :: [Fin N.Nat3]
-- [0,1,2]
inlineUniverse :: N.SNatI n => [Fin n]
inlineUniverse = getUniverse $ N.induction (Universe []) step where
    step :: Universe n -> Universe ('S n)
    step (Universe xs) = Universe (FZ : map FS xs)

-- | >>> inlineUniverse1 :: NonEmpty (Fin N.Nat3)
-- 0 :| [1,2]
inlineUniverse1 :: N.SNatI n => NonEmpty (Fin ('S n))
inlineUniverse1 = getUniverse1 $ N.induction (Universe1 (FZ :| [])) step where
    step :: Universe1 n -> Universe1 ('S n)
    step (Universe1 xs) = Universe1 (NE.cons FZ (fmap FS xs))

newtype Universe  n = Universe  { getUniverse  :: [Fin n] }
newtype Universe1 n = Universe1 { getUniverse1 :: NonEmpty (Fin ('S n)) }

-- | @'Fin' 'N.Nat0'@ is not inhabited.
absurd :: Fin N.Nat0 -> b
absurd n = case n of {}

-- | Counting to one is boring.
--
-- >>> boring
-- 0
boring :: Fin N.Nat1
boring = FZ

-------------------------------------------------------------------------------
-- min and max
-------------------------------------------------------------------------------

-- | Return a one less.
--
-- >>> isMin (FZ :: Fin N.Nat1)
-- Nothing
--
-- >>> map isMin universe :: [Maybe (Fin N.Nat3)]
-- [Nothing,Just 0,Just 1,Just 2]
--
-- @since 0.1.1
--
isMin :: Fin ('S n) -> Maybe (Fin n)
isMin FZ     = Nothing
isMin (FS n) = Just n

-- | Return a one less.
--
-- >>> isMax (FZ :: Fin N.Nat1)
-- Nothing
--
-- >>> map isMax universe :: [Maybe (Fin N.Nat3)]
-- [Just 0,Just 1,Just 2,Nothing]
--
-- @since 0.1.1
--
isMax :: forall n. N.SNatI n => Fin ('S n) -> Maybe (Fin n)
isMax = getIsMax (N.induction start step) where
    start :: IsMax 'Z
    start = IsMax $ \_ -> Nothing

    step :: IsMax m -> IsMax ('S m)
    step (IsMax rec) = IsMax $ \n -> case n of
        FZ   -> Just FZ
        FS m -> fmap FS (rec m)

newtype IsMax n = IsMax { getIsMax :: Fin ('S n) -> Maybe (Fin n) }

-------------------------------------------------------------------------------
-- Append & Split
-------------------------------------------------------------------------------

-- | >>> map weakenRight1 universe :: [Fin N.Nat5]
-- [1,2,3,4]
--
-- @since 0.1.1
weakenRight1 :: Fin n -> Fin ('S n)
weakenRight1 = FS

-- | >>> map weakenLeft1 universe :: [Fin N.Nat5]
-- [0,1,2,3]
--
-- @since 0.1.1
weakenLeft1 :: N.SNatI n => Fin n -> Fin ('S n)
weakenLeft1 = getWeaken1 (N.induction start step) where
    start :: Weaken1 'Z
    start = Weaken1 absurd

    step :: Weaken1 n -> Weaken1 ('S n)
    step (Weaken1 go) = Weaken1 $ \n -> case n of
        FZ    -> FZ
        FS n' -> FS (go n')

newtype Weaken1 n = Weaken1 { getWeaken1 :: Fin n -> Fin ('S n) }

-- | >>> map (weakenLeft (Proxy :: Proxy N.Nat2)) (universe :: [Fin N.Nat3])
-- [0,1,2]
weakenLeft :: forall n m. N.SNatI n => Proxy m -> Fin n -> Fin (N.Plus n m)
weakenLeft _ = getWeakenLeft (N.induction start step :: WeakenLeft m n) where
    start :: WeakenLeft m 'Z
    start = WeakenLeft absurd

    step :: WeakenLeft m p -> WeakenLeft m ('S p)
    step (WeakenLeft go) = WeakenLeft $ \n -> case n of
        FZ    -> FZ
        FS n' -> FS (go n')

newtype WeakenLeft m n = WeakenLeft { getWeakenLeft :: Fin n -> Fin (N.Plus n m) }

-- | >>> map (weakenRight (Proxy :: Proxy N.Nat2)) (universe :: [Fin N.Nat3])
-- [2,3,4]
weakenRight :: forall n m. N.SNatI n => Proxy n -> Fin m -> Fin (N.Plus n m)
weakenRight _ = getWeakenRight (N.induction start step :: WeakenRight m n) where
    start = WeakenRight id
    step (WeakenRight go) = WeakenRight $ \x -> FS $ go x

newtype WeakenRight m n = WeakenRight { getWeakenRight :: Fin m -> Fin (N.Plus n m) }

-- | Append two 'Fin's together.
--
-- >>> append (Left fin2 :: Either (Fin N.Nat5) (Fin N.Nat4))
-- 2
--
-- >>> append (Right fin2 :: Either (Fin N.Nat5) (Fin N.Nat4))
-- 7
--
append :: forall n m. N.SNatI n => Either (Fin n) (Fin m) -> Fin (N.Plus n m)
append (Left n)  = weakenLeft (Proxy :: Proxy m) n
append (Right m) = weakenRight (Proxy :: Proxy n) m

-- | Inverse of 'append'.
--
-- >>> split fin2 :: Either (Fin N.Nat2) (Fin N.Nat3)
-- Right 0
--
-- >>> split fin1 :: Either (Fin N.Nat2) (Fin N.Nat3)
-- Left 1
--
-- >>> map split universe :: [Either (Fin N.Nat2) (Fin N.Nat3)]
-- [Left 0,Left 1,Right 0,Right 1,Right 2]
--
split :: forall n m. N.SNatI n => Fin (N.Plus n m) -> Either (Fin n) (Fin m)
split = getSplit (N.induction start step) where
    start :: Split m 'Z
    start = Split Right

    step :: Split m p -> Split m ('S p)
    step (Split go) = Split $ \x -> case x of
        FZ    -> Left FZ
        FS x' -> bimap FS id $ go x'

newtype Split m n = Split { getSplit :: Fin (N.Plus n m) -> Either (Fin n) (Fin m) }

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

fin0 :: Fin (N.Plus N.Nat0 ('S n))
fin1 :: Fin (N.Plus N.Nat1 ('S n))
fin2 :: Fin (N.Plus N.Nat2 ('S n))
fin3 :: Fin (N.Plus N.Nat3 ('S n))
fin4 :: Fin (N.Plus N.Nat4 ('S n))
fin5 :: Fin (N.Plus N.Nat5 ('S n))
fin6 :: Fin (N.Plus N.Nat6 ('S n))
fin7 :: Fin (N.Plus N.Nat7 ('S n))
fin8 :: Fin (N.Plus N.Nat8 ('S n))
fin9 :: Fin (N.Plus N.Nat9 ('S n))

fin0 = FZ
fin1 = FS fin0
fin2 = FS fin1
fin3 = FS fin2
fin4 = FS fin3
fin5 = FS fin4
fin6 = FS fin5
fin7 = FS fin6
fin8 = FS fin7
fin9 = FS fin8
