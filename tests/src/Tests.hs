{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}

#if __GLASGOW_HASKELL__ <710
{-# OPTIONS_GHC -fcontext-stack=60 #-}
#endif
module Tests (main) where

import Data.Bin        (BinN (..))
import Data.Bin.Pos    (Pos, PosN)
import Data.Wid        (Wid)
import Data.Word       (Word64, Word8)
import Numeric.Natural (Natural)
import Test.Tasty      (TestTree, defaultMain, testGroup)

import qualified Data.Bin        as B
import qualified Data.Bin.Pos    as P
import qualified Data.Fin        as F
import qualified Data.Type.Bin   as B
import qualified Data.Type.Nat   as N
import qualified Data.Wid        as W
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
        , widTests
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
-- Wid
-------------------------------------------------------------------------------

widTests :: TestTree
widTests = testGroup "Data.Wid"
    [ bitsTests       wid8
    , bitsTests       wid64
    , finiteBitsTests wid8
    , finiteBitsTests wid64
    , ordTests        wid8
    , ordTests        wid64

    , testUniformity (QC.arbitrary :: QC.Gen (Wid N.Nat2)) id 4
    , testUniformity (QC.arbitrary :: QC.Gen (Wid N.Nat5)) id 32
    ]
  where
    wid8 :: Wid N.Nat8 -> Word8
    wid8 = fromIntegral . W.toNatural

    wid64 :: Wid (N.Mult N.Nat8 N.Nat8) -> Word64
    wid64 = fromIntegral . W.toNatural

-------------------------------------------------------------------------------
-- Bin
-------------------------------------------------------------------------------

binTests :: TestTree
binTests = testGroup "Data.Bin"
    [ bitsTests' False  B.toNatural
    , ordTests          B.toNatural
    , ordTests          B.toNaturalN
    , numTests          B.toNatural
    , numTests          B.toNaturalN
    ]

-------------------------------------------------------------------------------
-- Pos
-------------------------------------------------------------------------------

posTests :: TestTree
posTests = testGroup "Data.Pos"
    [ ordTests (P.toNatural  :: Pos B.Bin4   -> Natural)
    , ordTests (P.toNaturalN :: PosN B.BinN5 -> Natural)

    -- uniformity with binary pos is tricky
    , testUniformity (QC.arbitrary :: QC.Gen (Pos B.Bin2)) id 2
    , testUniformity (QC.arbitrary :: QC.Gen (Pos B.Bin5)) id 5
    , testUniformity (QC.arbitrary :: QC.Gen (Pos B.Bin7)) id 7

    , testUniformity (QC.arbitrary :: QC.Gen (PosN B.BinN2)) id 2
    , testUniformity (QC.arbitrary :: QC.Gen (PosN B.BinN5)) id 5
    , testUniformity (QC.arbitrary :: QC.Gen (PosN B.BinN7)) id 7

    , testUniformity (QC.arbitrary :: QC.Gen (PosN ('B1 ('B1 ('B1 ('B1 'BE)))))) id 31
    , testUniformity (QC.arbitrary :: QC.Gen (PosN ('B1 ('B1 ('B0 ('B1 'BE)))))) id 27
    ]
