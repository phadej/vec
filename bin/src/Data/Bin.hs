{-# LANGUAGE BangPatterns       #-}
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
    -- ** Data.Bits
    andN,
    xorN,
    complementBitN,
    clearBitN,
    -- * Aliases
    bin0, bin1, bin2, bin3, bin4, bin5, bin6, bin7, bin8, bin9,
    binN1, binN2, binN3, binN4, binN5, binN6, binN7, binN8, binN9,
    ) where

import Control.DeepSeq (NFData (..))
import Data.Bits       (Bits (..))
import Data.Data       (Data)
import Data.Hashable   (Hashable (..))
import Data.Monoid     (mappend)
import Data.Nat        (Nat (..))
import Data.Typeable   (Typeable)
import GHC.Exception   (ArithException (..), throw)
import Numeric.Natural (Natural)

import qualified Data.Nat        as N
import qualified Test.QuickCheck as QC

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

#if __GLASGOW_HASKELL__ < 710
deriving instance Typeable 'BZ
deriving instance Typeable 'BN
#endif

-- | Non-zero binary natural numbers.
--
-- We could have called this type @Bin1@,
-- but that's used as type alias for promoted @'BN' 'BE'@ in "Data.Type.Bin".
data BinN
    = BE        -- ^ one
    | B0 BinN  -- ^ mult2
    | B1 BinN  -- ^ mult2 plus 1
  deriving (Eq, Typeable, Data)

#if __GLASGOW_HASKELL__ < 710
deriving instance Typeable 'BE
deriving instance Typeable 'B0
deriving instance Typeable 'B1
#endif

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
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary Bin where
    arbitrary = QC.frequency [ (1, return BZ), (20, fmap BN QC.arbitrary) ]

    shrink BZ     = []
    shrink (BN b) = BZ : map BN (QC.shrink b)

instance QC.CoArbitrary Bin where
    coarbitrary = QC.coarbitrary . sp where
        sp :: Bin -> Maybe BinN
        sp BZ     = Nothing
        sp (BN n) = Just n

instance QC.Function Bin where
    function = QC.functionMap sp (maybe BZ BN) where
        sp :: Bin -> Maybe BinN
        sp BZ     = Nothing
        sp (BN n) = Just n

instance QC.Arbitrary BinN where
    arbitrary = do
        bs <- QC.arbitrary :: QC.Gen [Bool]
        return (foldr (\b -> if b then B1 else B0) BE bs)

    shrink BE     = []
    shrink (B1 b) = b : B0 b : map B1 (QC.shrink b)
    shrink (B0 b) = b : map B0 (QC.shrink b)

instance QC.CoArbitrary BinN where
    coarbitrary = QC.coarbitrary . sp where
        sp :: BinN -> Maybe (Either BinN BinN)
        sp BE     = Nothing
        sp (B0 b) = Just (Left b)
        sp (B1 b) = Just (Right b)

instance QC.Function BinN where
    function = QC.functionMap sp (maybe BE (either B0 B1)) where
        sp :: BinN -> Maybe (Either BinN BinN)
        sp BE     = Nothing
        sp (B0 b) = Just (Left b)
        sp (B1 b) = Just (Right b)

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
-- Bits
-------------------------------------------------------------------------------

instance Bits Bin where
    BZ   .&. _    = BZ
    _    .&. BZ   = BZ
    BN a .&. BN b = andN a b

    BZ   `xor` b    = b
    a    `xor` BZ   = a
    BN a `xor` BN b = xorN a b

    BZ   .|. b    = b
    a    .|. BZ   = a
    BN a .|. BN b = BN (a .|. b)

    bit = BN . bit

    clearBit BZ     _ = BZ
    clearBit (BN b) n = clearBitN b n

    complementBit BZ n     = bit n
    complementBit (BN b) n = complementBitN b n

    zeroBits = BZ

    shiftL BZ _     = BZ
    shiftL (BN b) n = BN (shiftL b n)

    shiftR BZ _ = BZ
    shiftR b n
        | n <= 0 = b
        | otherwise = shiftR (shiftR1 b) (pred n)

    rotateL = shiftL
    rotateR = shiftR

    testBit BZ _     = False
    testBit (BN b) i = testBit b i

    popCount BZ     = 0
    popCount (BN n) = popCount n

    -- xor -- tricky
    complement  _  = error "compelement @Bin is undefined"
    bitSizeMaybe _ = Nothing
    bitSize _      = error "bitSize @Bin is undefined"
    isSigned _     = False

andN :: BinN -> BinN -> Bin
andN BE     BE     = BN BE
andN BE     (B0 _) = BZ
andN BE     (B1 _) = BN BE
andN (B0 _) BE     = BZ
andN (B1 _) BE     = BN BE
andN (B0 a) (B0 b) = mult2 (andN a b)
andN (B0 a) (B1 b) = mult2 (andN a b)
andN (B1 a) (B0 b) = mult2 (andN a b)
andN (B1 a) (B1 b) = BN (mult2Plus1 (andN a b))

xorN :: BinN -> BinN -> Bin
xorN BE     BE     = BZ
xorN BE     (B0 b) = BN (B1 b)
xorN BE     (B1 b) = BN (B0 b)
xorN (B0 b) BE     = BN (B1 b)
xorN (B1 b) BE     = BN (B0 b)
xorN (B0 a) (B0 b) = mult2 (xorN a b)
xorN (B0 a) (B1 b) = BN (mult2Plus1 (xorN a b))
xorN (B1 a) (B0 b) = BN (mult2Plus1 (xorN a b))
xorN (B1 a) (B1 b) = mult2 (xorN a b)

clearBitN :: BinN -> Int -> Bin
clearBitN BE     0 = BZ
clearBitN BE     _ = BN BE
clearBitN (B0 b) 0 = BN (B0 b)
clearBitN (B0 b) n = mult2 (clearBitN b (pred n))
clearBitN (B1 b) 0 = BN (B0 b)
clearBitN (B1 b) n = BN (mult2Plus1 (clearBitN b (pred n)))

complementBitN :: BinN -> Int -> Bin
complementBitN BE     0 = BZ
complementBitN BE     n = BN (B1 (bit (pred n)))
complementBitN (B0 b) 0 = BN (B1 b)
complementBitN (B0 b) n = mult2 (complementBitN b (pred n))
complementBitN (B1 b) 0 = BN (B0 b)
complementBitN (B1 b) n = BN (mult2Plus1 (complementBitN b (pred n)))

shiftR1 :: Bin -> Bin
shiftR1 BZ          = BZ
shiftR1 (BN BE)     = BZ
shiftR1 (BN (B0 b)) = BN b
shiftR1 (BN (B1 b)) = BN b

-- | __NOTE__: '.&.', 'xor', 'shiftR' and 'rotateR' are __NOT_ implemented.
-- They may make number zero.
--
instance Bits BinN where
    B0 a .|. B0 b = B0 (a .|. b)
    B0 a .|. B1 b = B1 (a .|. b)
    B1 a .|. B0 b = B1 (a .|. b)
    B1 a .|. B1 b = B1 (a .|. b)

    BE   .|. B0 b = B1 b
    BE   .|. B1 b = B1 b
    B0 b .|. BE   = B1 b
    B1 b .|. BE   = B1 b

    BE   .|. BE   = BE

    bit n
        | n <= 0 = BE
        | otherwise = B0 (bit (pred n))

    shiftL b n
        | n <= 0    = b
        | otherwise = shiftL (B0 b) (pred n)

    rotateL = shiftL

    popCount = go 1 where
        go !acc BE     = acc
        go !acc (B0 b) = go acc b
        go !acc (B1 b) = go (succ acc) b

    testBit BE     0 = True
    testBit (B0 _) 0 = False
    testBit (B1 _) 0 = True
    testBit BE     _ = False
    testBit (B0 b) n = testBit b (pred n)
    testBit (B1 b) n = testBit b (pred n)

    zeroBits          = error "zeroBits @BinN is undefined"
    clearBit _ _      = error "clearBit @BinN is undefined"
    complementBit _ _ = error "complementBit @BinN is undefined"
    xor _ _           = error "xor @BinN is undefined"
    (.&.) _ _         = error "(.&.) @BinN is undefined"
    shiftR _          = error "shiftR @BinN is undefined"
    rotateR _         = error "shiftL @BinN is undefined"
    complement  _     = error "compelement @BinN is undefined"
    bitSizeMaybe _    = Nothing
    bitSize _         = error "bitSize @BinN is undefined"
    isSigned _        = True

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
