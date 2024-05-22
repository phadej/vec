{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE Safe               #-}
-- | Positive binary natural numbers, 'BinP'.
--
-- This module is designed to be imported qualified.
--
module Data.BinP (
    BinP(..),
    -- * Conversions
    cata,
    toNatural,
    fromNatural,
    toNat,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Extras
    predMaybe,
    -- * Aliases
    binP1, binP2, binP3, binP4, binP5, binP6, binP7, binP8, binP9,
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
-- BinP
-------------------------------------------------------------------------------

-- | Non-zero binary natural numbers.
--
-- We could have called this type @Bin1@,
-- but that's used as type alias for promoted @'BP' 'BE'@ in "Data.Type.Bin".
data BinP
    = BE        -- ^ one
    | B0 BinP  -- ^ mult2
    | B1 BinP  -- ^ mult2 plus 1
  deriving (Eq, Typeable, Data)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

-- |
--
-- >>> sort [ 1 .. 9 :: BinP ]
-- [1,2,3,4,5,6,7,8,9]
--
-- >>> sort $ reverse [ 1 .. 9 :: BinP ]
-- [1,2,3,4,5,6,7,8,9]
--
-- >>> sort $ [ 1 .. 9 ] ++ [ 1 .. 9 :: BinP ]
-- [1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9]
--
instance Ord BinP where
    compare = go EQ where
        go  acc BE     BE     = acc
        go _acc BE     _      = LT
        go _acc _      BE     = GT
        go  acc (B0 a) (B0 b) = go acc a b
        go  acc (B1 a) (B1 b) = go acc a b
        go _acc (B0 a) (B1 b) = go LT  a b
        go _acc (B1 a) (B0 b) = go GT  a b

instance Show BinP where
    showsPrec d = showsPrec d . toNatural

instance Num BinP where
    fromInteger = fromNatural . fromInteger

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

instance Real BinP where
    toRational = toRational . toInteger

instance Integral BinP where
    toInteger = toInteger . toNatural

    quotRem _ _ = error "quotRem @Bin is not implemented"

instance Enum BinP where
    succ BE     = B0 BE
    succ (B0 n) = B1 n
    succ (B1 n) = B0 (succ n)

    pred n = case predMaybe n of
        Nothing -> throw Underflow
        Just m  -> m

    toEnum n = case compare n 1 of
        LT -> throw Underflow
        EQ -> BE
        GT -> case n `divMod` 2 of
            (m, 0) -> B0 (toEnum m)
            (m, _) -> B1 (toEnum m)

    fromEnum BE     = 1
    fromEnum (B0 n) = 2 * fromEnum n
    fromEnum (B1 n) = succ (2 * fromEnum n)

instance NFData BinP where
    rnf BE     = ()
    rnf (B0 n) = rnf n
    rnf (B1 n) = rnf n

instance Hashable BinP where
    hashWithSalt = undefined

predMaybe :: BinP -> Maybe BinP
predMaybe BE     = Nothing
predMaybe (B1 n) = Just (B0 n)
predMaybe (B0 n) = Just (mult2Plus1 (predMaybe n))
  where
    mult2Plus1 :: Maybe BinP -> BinP
    mult2Plus1 = maybe BE B1

-------------------------------------------------------------------------------
-- Bits
-------------------------------------------------------------------------------

-- | __NOTE__: '.&.', 'xor', 'shiftR' and 'rotateR' are __NOT_ implemented.
-- They may make number zero.
--
instance Bits BinP where
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

    zeroBits          = error "zeroBits @BinP is undefined"
    clearBit _ _      = error "clearBit @BinP is undefined"
    complementBit _ _ = error "complementBit @BinP is undefined"
    xor _ _           = error "xor @BinP is undefined"
    (.&.) _ _         = error "(.&.) @BinP is undefined"
    shiftR _          = error "shiftR @BinP is undefined"
    rotateR _         = error "shiftL @BinP is undefined"
    complement  _     = error "compelement @BinP is undefined"
    bitSizeMaybe _    = Nothing
    bitSize _         = error "bitSize @BinP is undefined"
    isSigned _        = True

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary BinP where
    arbitrary = do
        bs <- QC.arbitrary :: QC.Gen [Bool]
        return (foldr (\b -> if b then B1 else B0) BE bs)

    shrink BE     = []
    shrink (B1 b) = b : B0 b : map B1 (QC.shrink b)
    shrink (B0 b) = b : map B0 (QC.shrink b)

instance QC.CoArbitrary BinP where
    coarbitrary = QC.coarbitrary . sp where
        sp :: BinP -> Maybe (Either BinP BinP)
        sp BE     = Nothing
        sp (B0 b) = Just (Left b)
        sp (B1 b) = Just (Right b)

instance QC.Function BinP where
    function = QC.functionMap sp (maybe BE (either B0 B1)) where
        sp :: BinP -> Maybe (Either BinP BinP)
        sp BE     = Nothing
        sp (B0 b) = Just (Left b)
        sp (B1 b) = Just (Right b)

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'BinP'.
--
-- >>> explicitShow 11
-- "B1 (B1 (B0 BE))"
explicitShow :: BinP -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'showsPrec' displaying a structure of 'BinP'.
explicitShowsPrec :: Int -> BinP -> ShowS
explicitShowsPrec _ BE
    = showString "BE"
explicitShowsPrec d (B0 n)
    = showParen (d > 10)
    $ showString "B0 "
    . explicitShowsPrec 11 n
explicitShowsPrec d (B1 n)
    = showParen (d > 10)
    $ showString "B1 "
    . explicitShowsPrec 11 n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | 'toNatural' for 'BinP'.
toNatural :: BinP -> Natural
toNatural BE     = 1
toNatural (B0 n) = 2 * toNatural n
toNatural (B1 n) = 2 * toNatural n + 1

-- | 'fromNatural' for 'BinP'.
--
-- Throws when given 0.
fromNatural :: Natural -> BinP
fromNatural 0 = throw Underflow
fromNatural 1 = BE
fromNatural n = case n `divMod` 2 of
    (m, 0) -> B0 (fromNatural m)
    (m, _) -> B1 (fromNatural m)

-- | Fold 'BinP'.
cata
    :: a        -- ^ \(1\)
    -> (a -> a) -- ^ \(2x\)
    -> (a -> a) -- ^ \(2x + 1\)
    -> BinP
    -> a
cata z o i = go where
    go BE     = z
    go (B0 b) = o (go b)
    go (B1 b) = i (go b)

-- | Convert from 'BinP' to 'Nat'.
toNat :: BinP -> Nat
toNat = cata (S Z) o i where
    o :: Nat -> Nat
    o = N.cata Z (S . S)

    i :: Nat -> Nat
    i = S . o

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

binP1, binP2, binP3, binP4, binP5, binP6, binP7, binP8, binP9 :: BinP
binP1 = BE
binP2 = B0 BE
binP3 = B1 BE
binP4 = B0 binP2
binP5 = B1 binP2
binP6 = B0 binP3
binP7 = B1 binP3
binP8 = B0 binP4
binP9 = B1 binP4
