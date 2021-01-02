{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}
#endif
-- | Binary natural numbers, 'Bin'.
--
-- This module is designed to be imported qualified.
--
module Data.Bin (
    -- * Binary natural numbers
    Bin(..),
    toNatural,
    fromNatural,
    toNat,
    fromNat,
    cata,
    -- * Positive natural numbers
    BinP (..),
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Extras
    predP,
    mult2,
    mult2Plus1,
    -- ** Data.Bits
    andP,
    xorP,
    complementBitP,
    clearBitP,
    -- * Aliases
    bin0, bin1, bin2, bin3, bin4, bin5, bin6, bin7, bin8, bin9,
    ) where

import Control.DeepSeq (NFData (..))
import Data.BinP       (BinP (..))
import Data.Bits       (Bits (..))
import Data.Data       (Data)
import Data.Hashable   (Hashable (..))
import Data.Nat        (Nat (..))
import Data.Typeable   (Typeable)
import GHC.Exception   (ArithException (..), throw)
import Numeric.Natural (Natural)

import qualified Data.BinP       as BP
import qualified Data.Nat        as N
import qualified Test.QuickCheck as QC

-- $setup
-- >>> import qualified Data.Nat as N

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
-- BP BE
-- BP (B0 BE)
-- BP (B1 BE)
-- BP (B0 (B0 BE))
-- BP (B1 (B0 BE))
-- BP (B0 (B1 BE))
-- BP (B1 (B1 BE))
--
data Bin
    = BZ          -- ^ zero
    | BP BP.BinP  -- ^ non-zero
  deriving (Eq, Ord, Typeable, Data)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ < 710
deriving instance Typeable 'BZ
deriving instance Typeable 'BP
#endif

-- | 'Bin' is printed as 'Natural'.
--
-- To see explicit structure, use 'explicitShow' or 'explicitShowsPrec'
--
instance Show Bin where
    showsPrec d = showsPrec d . toNatural

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
    b@(BP _) + BZ   = b
    BP a     + BP b = BP (a + b)

    BZ   * _    = BZ
    _    * BZ   = BZ
    BP a * BP b = BP (a * b)

    abs = id

    signum BZ      = BZ
    signum (BP _) = BP BE

    negate _ = error "negate @Bin"

instance Real Bin where
    toRational = toRational . toInteger

instance Integral Bin where
    toInteger = toInteger . toNatural

    quotRem _ _ = error "quotRem @Bin is not implemented"


-- | >>> take 10 $ iterate succ BZ
-- [0,1,2,3,4,5,6,7,8,9]
--
-- >>> take 10 [BZ ..]
-- [0,1,2,3,4,5,6,7,8,9]
--
instance Enum Bin where
    succ BZ = BP BE
    succ (BP n) = BP (succ n)

    pred BZ     = throw Underflow
    pred (BP n) = predP n

    toEnum n = case compare n 0 of
        LT -> throw Underflow
        EQ -> BZ
        GT -> BP (toEnum  n)

    fromEnum BZ     = 0
    fromEnum (BP n) = fromEnum n

instance NFData Bin where
    rnf BZ      = ()
    rnf (BP n) = rnf n

instance Hashable Bin where
    hashWithSalt = undefined

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | This is a total function.
--
-- >>> map predP [1..10]
-- [0,1,2,3,4,5,6,7,8,9]
--
predP :: BinP -> Bin
predP BE     = BZ
predP (B1 n) = BP (B0 n)
predP (B0 n) = BP (go n) where
    go :: BinP -- @00001xyz@
       -> BinP -- @11110xyz@
    go BE     = BE
    go (B1 m) = B1 (B0 m)
    go (B0 m) = B1 (go m)

mult2 :: Bin -> Bin
mult2 BZ     = BZ
mult2 (BP b) = BP (B0 b)

mult2Plus1 :: Bin -> BinP
mult2Plus1 BZ     = BE
mult2Plus1 (BP b) = B1 b

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary Bin where
    arbitrary = QC.frequency [ (1, return BZ), (20, fmap BP QC.arbitrary) ]

    shrink BZ     = []
    shrink (BP b) = BZ : map BP (QC.shrink b)

instance QC.CoArbitrary Bin where
    coarbitrary = QC.coarbitrary . sp where
        sp :: Bin -> Maybe BinP
        sp BZ     = Nothing
        sp (BP n) = Just n

instance QC.Function Bin where
    function = QC.functionMap sp (maybe BZ BP) where
        sp :: Bin -> Maybe BinP
        sp BZ     = Nothing
        sp (BP n) = Just n

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'Bin'.
--
-- >>> explicitShow 0
-- "BZ"
--
-- >>> explicitShow 2
-- "BP (B0 BE)"
--
explicitShow :: Bin -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'showsPrec' displaying a structure of 'Bin'.
explicitShowsPrec :: Int -> Bin -> ShowS
explicitShowsPrec _ BZ
    = showString "BZ"
explicitShowsPrec d (BP n)
    = showParen (d > 10)
    $ showString "BP "
    . BP.explicitShowsPrec 11 n

-------------------------------------------------------------------------------
-- Bits
-------------------------------------------------------------------------------

instance Bits Bin where
    BZ   .&. _    = BZ
    _    .&. BZ   = BZ
    BP a .&. BP b = andP a b

    BZ   `xor` b    = b
    a    `xor` BZ   = a
    BP a `xor` BP b = xorP a b

    BZ   .|. b    = b
    a    .|. BZ   = a
    BP a .|. BP b = BP (a .|. b)

    bit = BP . bit

    clearBit BZ     _ = BZ
    clearBit (BP b) n = clearBitP b n

    complementBit BZ n     = bit n
    complementBit (BP b) n = complementBitP b n

    zeroBits = BZ

    shiftL BZ _     = BZ
    shiftL (BP b) n = BP (shiftL b n)

    shiftR BZ _ = BZ
    shiftR b n
        | n <= 0 = b
        | otherwise = shiftR (shiftR1 b) (pred n)

    rotateL = shiftL
    rotateR = shiftR

    testBit BZ _     = False
    testBit (BP b) i = testBit b i

    popCount BZ     = 0
    popCount (BP n) = popCount n

    -- xor -- tricky
    complement  _  = error "compelement @Bin is undefined"
    bitSizeMaybe _ = Nothing
    bitSize _      = error "bitSize @Bin is undefined"
    isSigned _     = False

andP :: BinP -> BinP -> Bin
andP BE     BE     = BP BE
andP BE     (B0 _) = BZ
andP BE     (B1 _) = BP BE
andP (B0 _) BE     = BZ
andP (B1 _) BE     = BP BE
andP (B0 a) (B0 b) = mult2 (andP a b)
andP (B0 a) (B1 b) = mult2 (andP a b)
andP (B1 a) (B0 b) = mult2 (andP a b)
andP (B1 a) (B1 b) = BP (mult2Plus1 (andP a b))

xorP :: BinP -> BinP -> Bin
xorP BE     BE     = BZ
xorP BE     (B0 b) = BP (B1 b)
xorP BE     (B1 b) = BP (B0 b)
xorP (B0 b) BE     = BP (B1 b)
xorP (B1 b) BE     = BP (B0 b)
xorP (B0 a) (B0 b) = mult2 (xorP a b)
xorP (B0 a) (B1 b) = BP (mult2Plus1 (xorP a b))
xorP (B1 a) (B0 b) = BP (mult2Plus1 (xorP a b))
xorP (B1 a) (B1 b) = mult2 (xorP a b)

clearBitP :: BinP -> Int -> Bin
clearBitP BE     0 = BZ
clearBitP BE     _ = BP BE
clearBitP (B0 b) 0 = BP (B0 b)
clearBitP (B0 b) n = mult2 (clearBitP b (pred n))
clearBitP (B1 b) 0 = BP (B0 b)
clearBitP (B1 b) n = BP (mult2Plus1 (clearBitP b (pred n)))

complementBitP :: BinP -> Int -> Bin
complementBitP BE     0 = BZ
complementBitP BE     n = BP (B1 (bit (pred n)))
complementBitP (B0 b) 0 = BP (B1 b)
complementBitP (B0 b) n = mult2 (complementBitP b (pred n))
complementBitP (B1 b) 0 = BP (B0 b)
complementBitP (B1 b) n = BP (mult2Plus1 (complementBitP b (pred n)))

shiftR1 :: Bin -> Bin
shiftR1 BZ          = BZ
shiftR1 (BP BE)     = BZ
shiftR1 (BP (B0 b)) = BP b
shiftR1 (BP (B1 b)) = BP b

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
cata _ h e o (BP b) = BP.cata h e o b

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
toNat (BP n) = BP.toNat n

-- | Convert from 'Nat' to 'Bin'.
--
-- >>> fromNat 5
-- 5
--
-- >>> explicitShow (fromNat 5)
-- "BP (B1 (B0 BE))"
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
-- >>> toNatural $ BP $ B0 $ B1 $ BE
-- 6
--
toNatural :: Bin -> Natural
toNatural BZ        = 0
toNatural (BP bnz) = BP.toNatural bnz

-- | Convert 'Natural' to 'Nat'
--
-- >>> fromNatural 4
-- 4
--
-- >>> explicitShow (fromNatural 4)
-- "BP (B0 (B0 BE))"
--
fromNatural :: Natural -> Bin
fromNatural 0 = BZ
fromNatural n = BP (BP.fromNatural n)

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

bin0, bin1, bin2, bin3, bin4, bin5, bin6, bin7, bin8, bin9 :: Bin
bin0 = BZ
bin1 = BP BP.binP1
bin2 = BP BP.binP2
bin3 = BP BP.binP3
bin4 = BP BP.binP4
bin5 = BP BP.binP5
bin6 = BP BP.binP6
bin7 = BP BP.binP7
bin8 = BP BP.binP8
bin9 = BP BP.binP9
