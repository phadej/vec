{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE Safe                #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
-- | Fixed-'Wrd'th (unsigned) integers.
module Data.Wrd (
    Wrd (..),
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Conversions
    toNatural,
    -- * Universe
    universe,
    -- * Bits
    --
    -- | We have implementation of some 'Bits' members, which doesn't
    -- need 'N.SNatI' constraint.
    xor,
    (.&.),
    (.|.),
    complement,
    complement2,
    shiftR,
    shiftL,
    rotateL,
    rotateR,
    popCount,
    setBit,
    clearBit,
    complementBit,
    testBit,
    -- * Extras
    shiftL1,
    shiftR1,
    rotateL1,
    rotateR1,
    ) where

import Control.DeepSeq (NFData (..))
import Data.Hashable   (Hashable (..))
import Data.Nat        (Nat (..))
import Data.Proxy      (Proxy (..))
import Data.Typeable   (Typeable)
import Numeric.Natural (Natural)

import qualified Data.Type.Nat   as N
import qualified Test.QuickCheck as QC

import qualified Data.Bits as I (Bits (..), FiniteBits (..))

-- $setup
-- >>> :set -XDataKinds
-- >>> import Data.Nat (Nat(..))
-- >>> import qualified Data.Type.Nat as N

-------------------------------------------------------------------------------
-- Data
-------------------------------------------------------------------------------

-- | Fixed-width unsigned integers, 'Wrd's for short.
--
-- The number is thought to be stored in big-endian format,
-- i.e. most-significant bit first. (as in binary literals).
--
data Wrd (n :: Nat) where
    WE :: Wrd 'Z
    W0 :: Wrd n -> Wrd ('S n)
    W1 :: Wrd n -> Wrd ('S n)
  deriving (Typeable)

deriving instance Eq (Wrd n)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Ord (Wrd n) where
    compare WE WE = EQ
    compare (W0 a) (W0 b) = compare a b
    compare (W0 _) (W1 _) = LT
    compare (W1 _) (W0 _) = GT
    compare (W1 a) (W1 b) = compare a b

-- | 'Wrd' is printed as a binary literal.
--
-- >>> let i = W1 $ W0 $ W1 $ W0 WE
-- >>> i
-- 0b1010
--
-- >>> explicitShow i
-- "W1 $ W0 $ W1 $ W0 WE"
--
-- At the time being, there is no 'Num' instance.
--
instance Show (Wrd n) where
    showsPrec _ WE = showString "WE"
    showsPrec _ w  = showString "0b" . foldr f id (goBits w)
      where
        f True  acc = showChar '1' . acc
        f False acc = showChar '0' . acc

        goBits :: Wrd m -> [Bool]
        goBits WE = []
        goBits (W0 n) = False : goBits n
        goBits (W1 n) = True  : goBits n

instance NFData (Wrd n) where
    rnf WE     = ()
    rnf (W0 w) = rnf w
    rnf (W1 w) = rnf w

instance Hashable (Wrd n) where
    hashWithSalt salt WE     = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt (W0 w) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` w
    hashWithSalt salt (W1 w) = salt `hashWithSalt` (2 :: Int) `hashWithSalt` w

instance N.SNatI n => Bounded (Wrd n) where
    minBound = N.induction WE W0
    maxBound = N.induction WE W1

instance N.SNatI n => Num (Wrd n) where
    fromInteger = snd . wrdScanl0 f where
        f :: Integer -> (Integer, Bool)
        f i =
            let (i', m) = i `divMod` 2
            in (i', m /= 0)

    a + b = snd (wrdScanl2 f False a b) where
        f False False False = (False, False)
        f False False True  = (False, True)
        f False True  False = (False, True)
        f False True  True  = (True,  False)
        f True  False False = (False, True)
        f True  False True  = (True,  False)
        f True  True  False = (True,  False)
        f True  True  True  = (True,  True)

    a * b = snd $ fst $ wrdScanl f (a, I.zeroBits) b where
        f :: (Wrd n, Wrd n) -> Bool -> ((Wrd n, Wrd n), Bool)
        f (a', acc) True  = ((shiftL1 a', a' + acc), False)
        f (a', acc) False = ((shiftL1 a', acc), False)

    abs    = id
    negate = complement2

    signum = go False where
        go :: Bool -> Wrd m -> Wrd m
        go _     WE      = WE
        go True  (W0 WE) = W1 WE
        go False (W0 WE) = W0 WE
        go True  (W1 WE) = W1 WE
        go False (W1 WE) = W1 WE
        go b     (W0 w)  = W0 (go b w)
        go _     (W1 w)  = W0 (go True w)

-------------------------------------------------------------------------------
-- Bits & FiniteBits
-------------------------------------------------------------------------------

-- |
--
-- >>> let u = W0 $ W0 $ W1 $ W1 WE
-- >>> let v = W0 $ W1 $ W0 $ W1 WE
-- >>> (u, v)
-- (0b0011,0b0101)
--
-- >>> (complement u, complement v)
-- (0b1100,0b1010)
--
-- >>> (u .&. v, u .|. v, u `xor` v)
-- (0b0001,0b0111,0b0110)
--
-- >>> (shiftR v 1, shiftL v 1)
-- (0b0010,0b1010)
--
-- >>> (rotateR u 1, rotateL u 3)
-- (0b1001,0b1001)
--
-- >>> popCount u
-- 2
--
instance N.SNatI n => I.Bits (Wrd n) where
    complement = complement
    (.&.) = (.&.)
    (.|.) = (.|.)
    xor   = xor

    isSigned _ = False

    shiftR = shiftR
    shiftL = shiftL
    rotateR = rotateR
    rotateL = rotateL

    clearBit      = clearBit
    complementBit = complementBit
    setBit        = setBit
    testBit       = testBit

    zeroBits = N.induction WE W0

    popCount = popCount

    -- this is good enough
    bit = setBit I.zeroBits

    bitSizeMaybe = Just . I.finiteBitSize
    bitSize      = I.finiteBitSize

instance N.SNatI n => I.FiniteBits (Wrd n) where
    finiteBitSize _ = N.reflectToNum (Proxy :: Proxy n)

#if MIN_VERSION_base(4,8,0)
    countLeadingZeros = countLeadingZeros
#endif

testBit :: Wrd n -> Int -> Bool
testBit w0 i = snd (go 0 w0) where
    go :: Int -> Wrd n -> (Int, Bool)
    go j WE = (j, False)
    go j (W0 w) =
        let j''      = succ j'
            (j', b') = go j w
        in (j'', if i == j' then False else b')
    go j (W1 w) =
        let j''      = succ j'
            (j', b') = go j w
        in (j'', if i == j' then True else b')

clearBit          :: Wrd n -> Int -> Wrd n
clearBit      w i = mapWithBit (\j b -> if j == i then False else b) w

setBit            :: Wrd n -> Int -> Wrd n
setBit        w i = mapWithBit (\j b -> if j == i then True  else b) w

complementBit     :: Wrd n -> Int -> Wrd n
complementBit w i = mapWithBit (\j b -> if j == i then not b else b) w

complement :: Wrd n -> Wrd n
complement WE     = WE
complement (W0 w) = W1 (complement w)
complement (W1 w) = W0 (complement w)

-- | @'complement2' w = 'complement' w + 1@
complement2 :: Wrd n -> Wrd n
complement2 = snd . wrdScanl f True where
    f :: Bool -> Bool -> (Bool, Bool)
    f False False = (False, True)
    f False True  = (False, False)
    f True  False = (True,  False)
    f True  True  = (False, True)

(.&.) :: Wrd n -> Wrd n -> Wrd n
WE   .&. _    = WE
W1 a .&. W1 b = W1 (a .&. b)
W1 a .&. W0 b = W0 (a .&. b)
W0 a .&. W1 b = W0 (a .&. b)
W0 a .&. W0 b = W0 (a .&. b)

(.|.) :: Wrd n -> Wrd n -> Wrd n
WE   .|. _    = WE
W1 a .|. W1 b = W1 (a .|. b)
W1 a .|. W0 b = W1 (a .|. b)
W0 a .|. W1 b = W1 (a .|. b)
W0 a .|. W0 b = W0 (a .|. b)

xor :: Wrd n -> Wrd n -> Wrd n
xor WE      _     = WE
xor (W1 a) (W1 b) = W0 (xor a b)
xor (W1 a) (W0 b) = W1 (xor a b)
xor (W0 a) (W1 b) = W1 (xor a b)
xor (W0 a) (W0 b) = W0 (xor a b)

shiftR :: Wrd n -> Int -> Wrd n
shiftR w n
    | n <= 0 = w
    | otherwise = shiftR (shiftR1 w) (pred n)

shiftL :: Wrd n -> Int -> Wrd n
shiftL w n
    | n <= 0 = w
    | otherwise = shiftL (shiftL1 w) (pred n)

rotateR :: Wrd n -> Int -> Wrd n
rotateR w n
    | n <= 0 = w
    | otherwise = rotateR (rotateR1 w) (pred n)

rotateL :: Wrd n -> Int -> Wrd n
rotateL w n
    | n <= 0 = w
    | otherwise = rotateL (rotateL1 w) (pred n)

popCount :: Wrd n -> Int
popCount = go 0 where
    go :: Int -> Wrd m -> Int
    go !acc WE     = acc
    go !acc (W0 w) = go acc w
    go !acc (W1 w) = go (succ acc) w

shiftL1 :: Wrd n -> Wrd n
shiftL1 WE = WE
shiftL1 (W0 w) = pushBack w
shiftL1 (W1 w) = pushBack w

shiftR1 :: Wrd n -> Wrd n
shiftR1 WE       = WE
shiftR1 w@(W0 _) = W0 (dropLast w)
shiftR1 w@(W1 _) = W0 (dropLast w)

rotateL1 :: Wrd n -> Wrd n
rotateL1 WE = WE
rotateL1 (W0 w) = pushBack' w False
rotateL1 (W1 w) = pushBack' w True

rotateR1 :: Wrd n -> Wrd n
rotateR1 WE       = WE
rotateR1 w@(W0 _) = case dropLast' w of
    (True, w')  -> W1 w'
    (False, w') -> W0 w'
rotateR1 w@(W1 _) = case dropLast' w of
    (True, w')  -> W1 w'
    (False, w') -> W0 w'

pushBack ::  Wrd n ->  Wrd ('S n)
pushBack WE     = W0 WE
pushBack (W0 w) = W0 (pushBack w)
pushBack (W1 w) = W1 (pushBack w)

pushBack' ::  Wrd n -> Bool -> Wrd ('S n)
pushBack' WE     False = W0 WE
pushBack' WE     True  = W1 WE
pushBack' (W0 w) b     = W0 (pushBack' w b)
pushBack' (W1 w) b     = W1 (pushBack' w b)

dropLast :: Wrd ('S n) -> Wrd n
dropLast (W0 WE)       = WE
dropLast (W1 WE)       = WE
dropLast (W0 w@(W0 _)) = W0 (dropLast w)
dropLast (W0 w@(W1 _)) = W0 (dropLast w)
dropLast (W1 w@(W0 _)) = W1 (dropLast w)
dropLast (W1 w@(W1 _)) = W1 (dropLast w)

dropLast' :: Wrd ('S n) -> (Bool, Wrd n)
dropLast' (W0 WE)       = (False, WE)
dropLast' (W1 WE)       = (True, WE)
dropLast' (W0 w@(W0 _)) = fmap W0 (dropLast' w)
dropLast' (W0 w@(W1 _)) = fmap W0 (dropLast' w)
dropLast' (W1 w@(W0 _)) = fmap W1 (dropLast' w)
dropLast' (W1 w@(W1 _)) = fmap W1 (dropLast' w)

countLeadingZeros :: Wrd n -> Int
countLeadingZeros = go 0 where
    go :: Int -> Wrd m -> Int
    go !acc WE     = acc
    go !acc (W0 w) = go (succ acc) w
    go !acc (W1 _) = acc

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance N.SNatI n => QC.Arbitrary (Wrd n) where
    arbitrary = case N.snat :: N.SNat n of
        N.SZ -> return WE
        N.SS -> QC.oneof [ fmap W0 QC.arbitrary, fmap W1 QC.arbitrary ]

    shrink = shrink

shrink :: Wrd n -> [Wrd n]
shrink WE = []
shrink (W1 w) = W0 w : fmap W1 (shrink w)
shrink (W0 w) = fmap W0 (shrink w)

instance QC.CoArbitrary (Wrd n) where
    coarbitrary WE     = id
    coarbitrary (W0 w) = QC.coarbitrary (False, w)
    coarbitrary (W1 w) = QC.coarbitrary (True,  w)

instance N.SNatI n => QC.Function (Wrd n) where
    function = case N.snat :: N.SNat n of
        N.SZ -> QC.functionMap (const ()) (const WE)
        N.SS -> QC.functionMap toPair fromPair
      where
        toPair :: Wrd ('S m) -> (Bool, Wrd m)
        toPair (W0 w) = (False, w)
        toPair (W1 w) = (True,  w)

        fromPair :: (Bool, Wrd m) -> Wrd ('S m)
        fromPair (False, w) = W0 w
        fromPair (True,  w) = W1 w

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of @'Wrd' n@
--
-- >>> explicitShow WE
-- "WE"
--
-- >>> explicitShow $ W0 WE
-- "W0 WE"
--
-- >>> explicitShow $ W1 $ W0 $ W1 $ W0 WE
-- "W1 $ W0 $ W1 $ W0 WE"
--
explicitShow :: Wrd n -> String
explicitShow w = explicitShowsPrec 0 w ""

-- | 'showsPrec' displaying a structure of @'Wrd' n@.
--
-- >>> explicitShowsPrec 0 (W0 WE) ""
-- "W0 WE"
--
-- >>> explicitShowsPrec 1 (W0 WE) ""
-- "(W0 WE)"
--
explicitShowsPrec :: Int -> Wrd n -> ShowS
explicitShowsPrec _ WE = showString "WE"
explicitShowsPrec d w  = showParen (d > 0) $
    go (goBits w)
  where
    go []           = showString "WE"
    go [False]      = showString "W0 WE"
    go [True]       = showString "W1 WE"
    go (False : bs) = showString "W0 $ " . go bs
    go (True  : bs) = showString "W1 $ " . go bs

    goBits :: Wrd m -> [Bool]
    goBits WE = []
    goBits (W0 n) = False : goBits n
    goBits (W1 n) = True  : goBits n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert to 'Natural' number
--
-- >>> let u = W0 $ W1 $ W1 $ W1 $ W0 $ W1 $ W0 WE
-- >>> u
-- 0b0111010
--
-- >>> toNatural u
-- 58
--
-- >>> map toNatural (universe :: [Wrd N.Nat3])
-- [0,1,2,3,4,5,6,7]
--
toNatural :: Wrd n -> Natural
toNatural = go 0 where
    go :: Natural -> Wrd m -> Natural
    go !acc WE = acc
    go !acc (W0 w) = go (2 * acc)     w
    go !acc (W1 w) = go (2 * acc + 1) w

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- | All values, i.e. universe of @'Wrd' @.
--
-- >>> universe :: [Wrd 'Z]
-- [WE]
--
-- >>> universe :: [Wrd N.Nat3]
-- [0b000,0b001,0b010,0b011,0b100,0b101,0b110,0b111]
universe :: forall n. N.SNatI n => [Wrd n]
universe = getUniverse $ N.induction (Universe [WE]) go where
    go :: Universe m -> Universe ('S m)
    go (Universe u) = Universe (map W0 u ++ map W1 u)

newtype Universe n = Universe { getUniverse :: [Wrd n] }

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

mapWithBit :: (Int -> Bool -> Bool) -> Wrd n -> Wrd n
mapWithBit f = snd . wrdScanl g 0 where
    g i b = (succ i, f i b)

wrdScanl0 :: forall s n. N.SNatI n => (s -> (s, Bool)) -> s -> (s, Wrd n)
wrdScanl0 g = go where
    go :: forall m. N.SNatI m => s -> (s, Wrd m)
    go s = case N.snat :: N.SNat m of
        N.SZ -> (s, WE)
        N.SS ->
            let (s'', b)  = g s'
                (s' , w') = go s
            in (s'', if b then W1 w' else W0 w')

wrdScanl :: forall s n. (s -> Bool -> (s, Bool)) -> s ->  Wrd n -> (s, Wrd n)
wrdScanl g = go where
    go :: s -> Wrd m -> (s, Wrd m)
    go s WE = (s, WE)
    go s (W0 w) =
        let (s'', b)  = g s' False
            (s' , w') = go s w
        in (s'', if b then W1 w' else W0 w')
    go s (W1 w) =
        let (s'', b)  = g s' True
            (s' , w') = go s w
        in (s'', if b then W1 w' else W0 w')

wrdScanl2 :: forall s n. (s -> Bool -> Bool -> (s, Bool)) -> s ->  Wrd n -> Wrd n -> (s, Wrd n)
wrdScanl2 g = go where
    go :: s -> Wrd m -> Wrd m -> (s, Wrd m)
    go s WE _ = (s, WE)
    go s (W0 w) (W0 w') = go' s False False w w'
    go s (W0 w) (W1 w') = go' s False True  w w'
    go s (W1 w) (W0 w') = go' s True  False w w'
    go s (W1 w) (W1 w') = go' s True  True  w w'

    go' :: s -> Bool -> Bool -> Wrd m -> Wrd m -> (s, Wrd ('S m))
    go' s i j w u =
        let (s'', b)  = g s' i j
            (s' , v) = go s w u
        in (s'', if b then W1 v else W0 v)
