{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}

#if __GLASGOW_HASKELL__ <710
{-# OPTIONS_GHC -fcontext-stack=60 #-}
#endif
module Tests (main) where

import Data.Bin        (BinP (..))
import Data.Bin.Pos    (Pos, PosP)
import Data.Fiw        (Fiw)
import Data.Word       (Word64, Word8)
import Numeric.Natural (Natural)
import Test.Tasty      (TestTree, defaultMain, testGroup)

import qualified Data.Bin        as B
import qualified Data.Bin.Pos    as P
import qualified Data.BinP       as BP
import qualified Data.BinP.PosP  as PP
import qualified Data.Fin        as F
import qualified Data.Type.Bin   as B
import qualified Data.Type.BinP  as BP
import qualified Data.Type.Nat   as N
import qualified Data.Fiw        as W
import qualified Test.QuickCheck as QC

import Models
import Uniformity

main :: IO ()
main = defaultMain $ testGroup "packages"
    [ testGroup "fin"
        [ natTests
        , finTests
        ]

    , testGroup "bin"
        [ binTests
        , fiwTests
        , posTests
        ]

    , testGroup "sanity checks"
        [ testUniformity (QC.arbitrary :: QC.Gen Bool) id 2
        , testUniformity (QC.arbitrary :: QC.Gen Word8) (`div` 4) 64
        ]
    ]

-------------------------------------------------------------------------------
-- Nat
-------------------------------------------------------------------------------

natTests :: TestTree
natTests = testGroup "Data.Nat"
    [ ordTests          N.toNatural
    , numTests          N.toNatural
    ]

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

finTests :: TestTree
finTests = testGroup "Data.Fin"
    [ ordTests       (F.toNatural :: F.Fin N.Nat8 -> Natural)

    , testUniformity (QC.arbitrary :: QC.Gen (F.Fin N.Nat3)) id 2
    , testUniformity (QC.arbitrary :: QC.Gen (F.Fin N.Nat9)) id 8
    ]

-------------------------------------------------------------------------------
-- Fiw
-------------------------------------------------------------------------------

fiwTests :: TestTree
fiwTests = testGroup "Data.Fiw"
    [ bitsTests       fiw8
    , bitsTests       fiw64
    , finiteBitsTests fiw8
    , finiteBitsTests fiw64
    , ordTests        fiw8
    , ordTests        fiw64

    , testUniformity (QC.arbitrary :: QC.Gen (Fiw N.Nat2)) id 4
    , testUniformity (QC.arbitrary :: QC.Gen (Fiw N.Nat5)) id 32
    ]
  where
    fiw8 :: Fiw N.Nat8 -> Word8
    fiw8 = fromIntegral . W.toNatural

    fiw64 :: Fiw (N.Mult N.Nat8 N.Nat8) -> Word64
    fiw64 = fromIntegral . W.toNatural

-------------------------------------------------------------------------------
-- Bin
-------------------------------------------------------------------------------

binTests :: TestTree
binTests = testGroup "Data.Bin"
    [ bitsTests' False  B.toNatural
    , ordTests          B.toNatural
    , ordTests          BP.toNatural
    , numTests          B.toNatural
    , numTests          BP.toNatural
    ]

-------------------------------------------------------------------------------
-- Pos
-------------------------------------------------------------------------------

posTests :: TestTree
posTests = testGroup "Data.Pos"
    [ ordTests (P.toNatural  :: Pos B.Bin4    -> Natural)
    , ordTests (PP.toNatural :: PosP BP.BinP5 -> Natural)

    -- uniformity with binary pos is tricky
    , testUniformity (QC.arbitrary :: QC.Gen (Pos B.Bin2)) id 2
    , testUniformity (QC.arbitrary :: QC.Gen (Pos B.Bin5)) id 5
    , testUniformity (QC.arbitrary :: QC.Gen (Pos B.Bin7)) id 7

    , testUniformity (QC.arbitrary :: QC.Gen (PosP BP.BinP2)) id 2
    , testUniformity (QC.arbitrary :: QC.Gen (PosP BP.BinP5)) id 5
    , testUniformity (QC.arbitrary :: QC.Gen (PosP BP.BinP7)) id 7

    , testUniformity (QC.arbitrary :: QC.Gen (PosP ('B1 ('B1 ('B1 ('B1 'BE)))))) id 31
    , testUniformity (QC.arbitrary :: QC.Gen (PosP ('B1 ('B1 ('B0 ('B1 'BE)))))) id 27
    ]
