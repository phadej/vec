{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Main (main) where

import Data.Tagged     (Tagged (..), retag)
import GHC.Generics    (Generic)
import Test.Inspection

import qualified Data.Fin      as F
import qualified Data.Fin.Enum as E
import qualified Data.Type.Nat as N

-------------------------------------------------------------------------------
-- InlineInduction
-------------------------------------------------------------------------------

-- | This doesn't evaluate compile time.
lhsInline :: Int
lhsInline = unTagged (N.inlineInduction1 (pure 0) (retag . fmap succ) :: Tagged N.Nat5 Int)

-- | This doesn't evaluate compile time.
lhsNormal :: Int
lhsNormal = unTagged (N.induction1 (pure 0) (retag . fmap succ) :: Tagged N.Nat5 Int)

rhs :: Int
rhs = 5

inspect $ 'lhsInline === 'rhs
inspect $ 'lhsNormal =/= 'rhs

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

-- | Note: GHC 8.0 (but not GHC 8.2?) seems to be
-- so smart, it reuses dictionary value.
--
-- Therefore, we define own local Ordering'
data Ordering' = LT' | EQ' | GT' deriving (Generic)

lhsEnum :: Ordering' -> F.Fin N.Nat3
lhsEnum = E.gfrom

rhsEnum :: Ordering' -> F.Fin N.Nat3
rhsEnum LT' = F.Z
rhsEnum EQ' = F.S F.Z
rhsEnum GT' = F.S (F.S F.Z)

inspect $  'lhsEnum ==- 'rhsEnum

-------------------------------------------------------------------------------
-- Main to make GHC happy
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
