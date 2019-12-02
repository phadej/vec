{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Models where

import Data.Bits     (Bits (..), FiniteBits (..))
import Data.Proxy    (Proxy (..))
import Data.Typeable (Typeable, typeRep)
import Test.Tasty    (TestTree, testGroup)

import qualified Test.QuickCheck as QC

import ModelTest

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

ordTests
    :: forall a b. (Typeable a, Typeable b, Ord a, Ord b, Show a, Show b, QC.Arbitrary a)
    => (a -> b)
    -> TestTree
ordTests a2b = testGroup ("Ord: " ++ nameA ++ " compared to " ++ nameB)
    [ modelTest a2b constraint "compare" (mapAAX compare)
    ]
  where
    nameA      = show $ typeRep (Proxy :: Proxy a)
    nameB      = show $ typeRep (Proxy :: Proxy b)
    constraint = Proxy :: Proxy Ord

-------------------------------------------------------------------------------
-- Num
-------------------------------------------------------------------------------

numTests
    :: forall a b. (Typeable a, Typeable b, Num a, Num b, Show a, Show b, QC.Arbitrary a, Eq b)
    => (a -> b)
    -> TestTree
numTests = numTests' True

numTests'
    :: forall a b. (Typeable a, Typeable b, Num a, Num b, Show a, Show b, QC.Arbitrary a, Eq b)
    => Bool -- negate
    -> (a -> b)
    -> TestTree
numTests' neg a2b = testGroup ("Num: " ++ nameA ++ " compared to " ++ nameB) $
    [ modelTest a2b constraint "(+)"    (mapAAA (+))
    , modelTest a2b constraint "(*)"    (mapAAA (*))
    , modelTest a2b constraint "signum" (mapAA signum)
    , modelTest a2b constraint "abs"    (mapAA abs)
    ]
    ++ [ modelTest a2b constraint "(-)"         (mapAAA (-))          | neg ]
    ++ [ modelTest a2b constraint "negate"      (mapAA negate)        | neg ]
    ++ [ modelTest a2b constraint "fromInteger" (mapXA fromInteger)   | neg ]
  where
    nameA      = show $ typeRep (Proxy :: Proxy a)
    nameB      = show $ typeRep (Proxy :: Proxy b)
    constraint = Proxy :: Proxy Num

-------------------------------------------------------------------------------
-- Bits
-------------------------------------------------------------------------------

bitsTests
    :: forall a b. (Typeable a, Typeable b, Bits a, Bits b, Show a, Show b, QC.Arbitrary a)
    => (a -> b)
    -> TestTree
bitsTests = bitsTests' True

bitsTests'
    :: forall a b. (Typeable a, Typeable b, Bits a, Bits b, Show a, Show b, QC.Arbitrary a)
    => Bool      -- ^ include 'complement'
    -> (a -> b)
    -> TestTree
bitsTests' testComplement a2b = testGroup ("Bits: " ++ nameA ++ " compared to " ++ nameB) $
    [ modelTest a2b constraint "complement"    (mapAA complement) | testComplement ] ++
    [ modelTest a2b constraint "isSigned"      (mapAX isSigned)
    , modelTest a2b constraint "popCount"      (mapAX popCount)
    , modelTest a2b constraint ".&."           (mapAAA (.&.))
    , modelTest a2b constraint ".|."           (mapAAA (.|.))
    , modelTest a2b constraint "xor"           (mapAAA xor)
    , modelTest a2b constraint "shift"         (mapAXA shift)
    , modelTest a2b constraint "rotate"        (mapAXA rotate)
#if !MIN_VERSION_base(4,9,0) || MIN_VERSION_base(4,10,0)
    -- broken Natural clearBit in base-4.9
    , modelTest a2b constraint "clearBit"      (mapAXA $ limitBits clearBit)
#endif
    , modelTest a2b constraint "setBit"        (mapAXA $ limitBits setBit)
    , modelTest a2b constraint "complementBit" (mapAXA $ limitBits complementBit)
    , modelTest a2b constraint "testBit"       (mapAXY $ limitBits testBit)
    , modelTest a2b constraint "zeroBits"      (mapUA zeroBits)
    ]
  where
    nameA      = show $ typeRep (Proxy :: Proxy a)
    nameB      = show $ typeRep (Proxy :: Proxy b)
    constraint = Proxy :: Proxy Bits

limitBits :: (a -> Int -> b) -> a -> Int -> b
limitBits f x b = f x (abs b)

-------------------------------------------------------------------------------
-- FiniteBits
-------------------------------------------------------------------------------

finiteBitsTests
    :: forall a b. (Typeable a, Typeable b, FiniteBits a, FiniteBits b, Show a, Show b, QC.Arbitrary a)
    => (a -> b)
    -> TestTree
finiteBitsTests a2b = testGroup ("FiniteBits: " ++ nameA ++ " compared to " ++ nameB)
    [ modelTest a2b constraint "finiteBitSize"     (mapAX finiteBitSize)
#if MIN_VERSION_base(4,8,0)
    , modelTest a2b constraint "countLeadingZeros" (mapAX countLeadingZeros)
#endif
    ]
  where
    nameA      = show $ typeRep (Proxy :: Proxy a)
    nameB      = show $ typeRep (Proxy :: Proxy b)
    constraint = Proxy :: Proxy FiniteBits
