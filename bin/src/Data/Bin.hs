{-# LANGUAGE DeriveDataTypeable #-}
-- | Binary natural numbers, 'Bin'.
--
-- This module is designed to be imported qualified.
--
module Data.Bin (
    -- * Binary natural numbers
    Bin(..),
    BinN(..),
    toNatural,
    toNaturalN,
    fromNatural,
    fromNaturalN,
    toNat,
    toNatN,
    fromNat,
    cata,
    cataN,
    -- * Showing
    explicitShow,
    explicitShowN,
    explicitShowsPrec,
    explicitShowsPrecN,
    -- * Extras
    predN,
    mult2,
    mult2Plus1,
    -- * Aliases
    bin0, bin1, bin2, bin3, bin4, bin5, bin6, bin7, bin8, bin9,
    binN1, binN2, binN3, binN4, binN5, binN6, binN7, binN8, binN9,
    ) where

import Control.DeepSeq (NFData (..))
import Data.Data       (Data)
import Data.Hashable   (Hashable (..))
import Data.Monoid     (mappend)
import Data.Nat        (Nat (..))
import Data.Typeable   (Typeable)
import GHC.Exception   (ArithException (..), throw)
import Numeric.Natural (Natural)

import qualified Data.Nat as N

-- $setup
-- >>> import Data.List (sort)

-------------------------------------------------------------------------------
-- Bin
-------------------------------------------------------------------------------

-- | Binary natural numbers.
--
-- Numbers are represented in little-endian order,
-- the representation is unique.
--
-- >>> mapM_ (putStrLn .  explicitShow) [0 .. 7]
-- BZ
-- BN BE
-- BN (B0 BE)
-- BN (B1 BE)
-- BN (B0 (B0 BE))
-- BN (B1 (B0 BE))
-- BN (B0 (B1 BE))
-- BN (B1 (B1 BE))
--
data Bin
    = BZ          -- ^ zero
    | BN BinN    -- ^ non-zero
  deriving (Eq, Ord, Typeable, Data)

-- | Non-zero binary natural numbers.
--
-- We could have called this type @Bin1@,
-- but that's used as type alias for promoted @'BN' 'BE'@ in "Data.Type.Bin".
data BinN
    = BE        -- ^ one
    | B0 BinN  -- ^ mult2
    | B1 BinN  -- ^ mult2 plus 1
  deriving (Eq, Typeable, Data)

-- >>> sort [0 .. 9 :: Bin]
-- [0,1,2,3,4,5,6,7,8,9]
--
instance Ord BinN where
    compare BE     BE     = EQ
    compare BE     _      = LT
    compare _      BE     = GT
    compare (B0 a) (B0 b) = compare a b
    compare (B1 a) (B1 b) = compare a b
    compare (B0 a) (B1 b) = compare a b `mappend` LT
    compare (B1 a) (B0 b) = compare a b `mappend` GT

-- | 'Bin' is printed as 'Natural'.
--
-- To see explicit structure, use 'explicitShow' or 'explicitShowsPrec'
--
instance Show Bin where
    showsPrec d = showsPrec d . toNatural

instance Show BinN where
    showsPrec d = showsPrec d . toNaturalN

-- |
--
-- >>> 0 + 2 :: Bin
-- 2
--
-- >>> 1 + 2 :: Bin
-- 3
--
-- >>> 4 * 8 :: Bin
-- 32
--
-- >>> 7 * 7 :: Bin
-- 49
--
instance Num Bin where
    fromInteger = fromNatural . fromInteger

    BZ       + b    = b
    b@(BN _) + BZ   = b
    BN a     + BN b = BN (a + b)

    BZ   * _    = BZ
    _    * BZ   = BZ
    BN a * BN b = BN (a * b)

    abs = id

    signum BZ      = BZ
    signum (BN _) = BN BE

    negate _ = error "negate @Bin"

instance Num BinN where
    fromInteger = fromNaturalN . fromInteger

    BE   + b    = succ b
    b    + BE   = succ b
    B0 a + B0 b = B0 (a + b)
    B0 a + B1 b = B1 (a + b)
    B1 a + B0 b = B1 (a + b)
    B1 a + B1 b = B0 (succ (a + b))

    BE * b = b
    a  * BE = a
    B0 a * B0 b = B0 (B0 (a * b))
    B1 a * B0 b = B0 (B0 (a * b)) + B0 b
    B0 a * B1 b = B0 (B0 (a * b)) + B0 a
    B1 a * B1 b = B1 (B0 (a * b)) + B0 a + B0 b

    abs = id

    signum _ = BE

    negate _ = error "negate @Bin"


instance Real Bin where
    toRational = toRational . toInteger

instance Real BinN where
    toRational = toRational . toInteger

instance Integral Bin where
    toInteger = toInteger . toNatural

    quotRem _ _ = error "quotRem @Bin is not implemented"

instance Integral BinN where
    toInteger = toInteger . toNaturalN

    quotRem _ _ = error "quotRem @Bin is not implemented"

-- | >>> take 10 $ iterate succ BZ
-- [0,1,2,3,4,5,6,7,8,9]
--
-- >>> take 10 [BZ ..]
-- [0,1,2,3,4,5,6,7,8,9]
--
instance Enum Bin where
    succ BZ = BN BE
    succ (BN n) = BN (succ n)

    pred BZ     = throw Underflow
    pred (BN n) = predN n

    toEnum n = case compare n 0 of
        LT -> throw Underflow
        EQ -> BZ
        GT -> BN (toEnum  n)

    fromEnum BZ     = 0
    fromEnum (BN n) = fromEnum n

instance Enum BinN where
    succ BE     = B0 BE
    succ (B0 n) = B1 n
    succ (B1 n) = B0 (succ n)

    pred n = case predN n of
        BZ   -> throw Underflow
        BN m -> m

    toEnum n = case compare n 1 of
        LT -> throw Underflow
        EQ -> BE
        GT -> case n `divMod` 2 of
            (m, 0) -> B0 (toEnum m)
            (m, _) -> B1 (toEnum m)

    fromEnum BE     = 1
    fromEnum (B0 n) = 2 * fromEnum n
    fromEnum (B1 n) = succ (2 * fromEnum n)

instance NFData Bin where
    rnf BZ      = ()
    rnf (BN n) = rnf n

instance NFData BinN where
    rnf BE     = ()
    rnf (B0 n) = rnf n
    rnf (B1 n) = rnf n

instance Hashable Bin where
    hashWithSalt = undefined

instance Hashable BinN where
    hashWithSalt = undefined

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | This is a total function.
--
-- >>> map predN [1..10]
-- [0,1,2,3,4,5,6,7,8,9]
--
predN :: BinN -> Bin
predN BE     = BZ
predN (B1 n) = BN (B0 n)
predN (B0 n) = BN (mult2Plus1 (predN n))

mult2 :: Bin -> Bin
mult2 BZ     = BZ
mult2 (BN b) = BN (B0 b)

mult2Plus1 :: Bin -> BinN
mult2Plus1 BZ     = BE
mult2Plus1 (BN b) = B1 b

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'Bin'.
--
-- >>> explicitShow 0
-- "BZ"
--
-- >>> explicitShow 2
-- "BN (B0 BE)"
--
explicitShow :: Bin -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'show' displaying a structure of 'BinN'.
--
-- >>> explicitShow 11
-- "BN (B1 (B1 (B0 BE)))"
explicitShowN :: BinN -> String
explicitShowN n = explicitShowsPrecN 0 n ""

-- | 'showsPrec' displaying a structure of 'Bin'.
explicitShowsPrec :: Int -> Bin -> ShowS
explicitShowsPrec _ BZ
    = showString "BZ"
explicitShowsPrec d (BN n)
    = showParen (d > 10)
    $ showString "BN "
    . explicitShowsPrecN 11 n

-- | 'showsPrec' displaying a structure of 'BinN'.
explicitShowsPrecN :: Int -> BinN -> ShowS
explicitShowsPrecN _ BE
    = showString "BE"
explicitShowsPrecN d (B0 n)
    = showParen (d > 10)
    $ showString "B0 "
    . explicitShowsPrecN 11 n
explicitShowsPrecN d (B1 n)
    = showParen (d > 10)
    $ showString "B1 "
    . explicitShowsPrecN 11 n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Fold 'Bin'.
cata
    :: a        -- ^ \(0\)
    -> a        -- ^ \(1\)
    -> (a -> a) -- ^ \(2x\)
    -> (a -> a) -- ^ \(2x + 1\)
    -> Bin
    -> a
cata z _ _ _ BZ     = z
cata _ h e o (BN b) = cataN h e o b

-- | Fold 'BinN'.
cataN
    :: a        -- ^ \(1\)
    -> (a -> a) -- ^ \(2x\)
    -> (a -> a) -- ^ \(2x + 1\)
    -> BinN
    -> a
cataN z o i = go where
    go BE     = z
    go (B0 b) = o (go b)
    go (B1 b) = i (go b)

-- | Convert from 'Bin' to 'Nat'.
--
-- >>> toNat 5
-- 5
--
-- >>> N.explicitShow (toNat 5)
-- "S (S (S (S (S Z))))"
--
toNat :: Bin -> Nat
toNat BZ     = Z
toNat (BN n) = toNatN n

-- | Convert from 'BinN' to 'Nat'.
toNatN :: BinN -> Nat
toNatN = cataN (S Z) o i where
    o :: Nat -> Nat
    o = N.cata Z (S . S)

    i :: Nat -> Nat
    i = S . o

-- | Convert from 'Nat' to 'Bin'.
--
-- >>> fromNat 5
-- 5
--
-- >>> explicitShow (fromNat 5)
-- "BN (B1 (B0 BE))"
--
fromNat :: Nat -> Bin
fromNat = N.cata BZ succ

-- | Convert 'Bin' to 'Natural'
--
-- >>> toNatural 0
-- 0
--
-- >>> toNatural 2
-- 2
--
-- >>> toNatural $ BN $ B0 $ B1 $ BE
-- 6
--
toNatural :: Bin -> Natural
toNatural BZ        = 0
toNatural (BN bnz) = toNaturalN bnz

-- | 'toNatural' for 'BinN'.
toNaturalN :: BinN -> Natural
toNaturalN BE     = 1
toNaturalN (B0 n) = 2 * toNaturalN n
toNaturalN (B1 n) = 2 * toNaturalN n + 1

-- | Convert 'Natural' to 'Nat'
--
-- >>> fromNatural 4
-- 4
--
-- >>> explicitShow (fromNatural 4)
-- "BN (B0 (B0 BE))"
--
fromNatural :: Natural -> Bin
fromNatural 0 = BZ
fromNatural n = BN (fromNaturalN n)

-- | 'fromNatural' for 'BinN'.
--
-- Throws when given 0.
fromNaturalN :: Natural -> BinN
fromNaturalN 0 = throw Underflow
fromNaturalN 1 = BE
fromNaturalN n = case n `divMod` 2 of
    (m, 0) -> B0 (fromNaturalN m)
    (m, _) -> B1 (fromNaturalN m)

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

bin0, bin1, bin2, bin3, bin4, bin5, bin6, bin7, bin8, bin9 :: Bin
bin0 = BZ
bin1 = BN binN1
bin2 = BN binN2
bin3 = BN binN3
bin4 = BN binN4
bin5 = BN binN5
bin6 = BN binN6
bin7 = BN binN7
bin8 = BN binN8
bin9 = BN binN9

binN1, binN2, binN3, binN4, binN5, binN6, binN7, binN8, binN9 :: BinN
binN1 = BE
binN2 = B0 BE
binN3 = B1 BE
binN4 = B0 binN2
binN5 = B1 binN2
binN6 = B0 binN3
binN7 = B1 binN3
binN8 = B0 binN4
binN9 = B1 binN4
