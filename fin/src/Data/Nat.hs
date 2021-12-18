{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE Safe               #-}

#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}
#endif
-- | 'Nat' numbers.
--
-- This module is designed to be imported qualified.
--
module Data.Nat (
    -- * Natural, Nat numbers
    Nat(..),
    toNatural,
    fromNatural,
    cata,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Aliases
    nat0, nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9,
    ) where

import Control.DeepSeq (NFData (..))
import Data.Data       (Data)
import Data.Hashable   (Hashable (..))
import Data.Typeable   (Typeable)
import GHC.Exception   (ArithException (..), throw)
import Numeric.Natural (Natural)

import qualified Data.Universe.Class as U
import qualified Test.QuickCheck     as QC

-- $setup

-------------------------------------------------------------------------------
-- Nat
-------------------------------------------------------------------------------

-- | Nat natural numbers.
--
-- Better than GHC's built-in 'GHC.TypeLits.Nat' for some use cases.
--
data Nat = Z | S Nat deriving (Eq, Typeable, Data)

#if __GLASGOW_HASKELL__ < 710
deriving instance Typeable 'Z
deriving instance Typeable 'S
#endif

-- | 'Nat' is printed as 'Natural'.
--
-- To see explicit structure, use 'explicitShow' or 'explicitShowsPrec'
--
instance Show Nat where
    showsPrec d = showsPrec d . toNatural

instance Ord Nat where
    compare Z     Z     = EQ
    compare Z     (S _) = LT
    compare (S _) Z     = GT
    compare (S n) (S m) = compare n m

    Z   <= _   = True
    S _ <= Z   = False
    S n <= S m = n <= m

    n <  m = not (m <= n)
    n >  m = not (n <= m)
    n >= m = m <= n

    min Z     _     = Z
    min (S _) Z     = Z
    min (S n) (S m) = S (min n m)

    max Z       Z       = Z
    max Z       m@(S _) = m
    max n@(S _) Z       = n
    max (S n)   (S m)   = S (max n m)

instance Num Nat where
    fromInteger = fromNatural . fromInteger

    Z   + m = m
    S n + m = S (n + m)

    Z   * _ = Z
    S n * m = (n * m) + m

    abs = id

    signum Z     = Z
    signum (S _) = S Z

    negate _ = error "negate @Nat"

instance Real Nat where
    toRational = toRational . toInteger

instance Integral Nat where
    toInteger = cata 0 succ

    quotRem _ Z = throw DivideByZero
    quotRem _ _ = error "quotRam @Nat un-implemented"

{- TODO: make <= with witness
instance Ix Nat where
    range = _

    inRange = _
-}

instance Enum Nat where
    toEnum n
        | n < 0     = throw Underflow
        | otherwise = iterate S Z !! n

    fromEnum = cata 0 succ

    succ       = S
    pred Z     = throw Underflow
    pred (S n) = n

instance NFData Nat where
    rnf Z     = ()
    rnf (S n) = rnf n

instance Hashable Nat where
    hashWithSalt salt = hashWithSalt salt . toInteger

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary Nat where
    arbitrary = fmap fromNatural QC.arbitrarySizedNatural

    shrink Z     = []
    shrink (S n) = n : QC.shrink n

instance QC.CoArbitrary Nat where
    coarbitrary Z     = QC.variant (0 :: Int)
    coarbitrary (S n) = QC.variant (1 :: Int) . QC.coarbitrary n

instance QC.Function Nat where
    function = QC.functionIntegral

-------------------------------------------------------------------------------
-- universe-base
-------------------------------------------------------------------------------

-- |
--
-- >>> import qualified Data.Universe.Class as U
-- >>> take 10 (U.universe :: [Nat])
-- [0,1,2,3,4,5,6,7,8,9]
--
-- @since 0.1.2
instance U.Universe Nat where
    universe = go Z where
        go n = n : go (S n)

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'Nat'.
--
-- >>> explicitShow 0
-- "Z"
--
-- >>> explicitShow 2
-- "S (S Z)"
--
explicitShow :: Nat -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'showsPrec' displaying a structure of 'Nat'.
explicitShowsPrec :: Int -> Nat -> ShowS
explicitShowsPrec _ Z     = showString "Z"
explicitShowsPrec d (S n) = showParen (d > 10)
    $ showString "S "
    . explicitShowsPrec 11 n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Fold 'Nat'.
--
-- >>> cata [] ('x' :) 2
-- "xx"
--
cata :: a -> (a -> a) -> Nat -> a
cata z f = go where
    go Z     = z
    go (S n) = f (go n)

-- | Convert 'Nat' to 'Natural'
--
-- >>> toNatural 0
-- 0
--
-- >>> toNatural 2
-- 2
--
-- >>> toNatural $ S $ S $ Z
-- 2
--
toNatural :: Nat -> Natural
toNatural Z = 0
toNatural (S n) = succ (toNatural n)

-- | Convert 'Natural' to 'Nat'
--
-- >>> fromNatural 4
-- 4
--
-- >>> explicitShow (fromNatural 4)
-- "S (S (S (S Z)))"
--
fromNatural :: Natural -> Nat
fromNatural 0 = Z
fromNatural n = S (fromNatural (pred n))

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

nat0, nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9 :: Nat
nat0 = Z
nat1 = S nat0
nat2 = S nat1
nat3 = S nat2
nat4 = S nat3
nat5 = S nat4
nat6 = S nat5
nat7 = S nat6
nat8 = S nat7
nat9 = S nat8
