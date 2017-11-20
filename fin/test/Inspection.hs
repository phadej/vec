{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Main (main) where

import Data.Tagged     (Tagged (..), retag)
import Test.Inspection

import qualified Data.Type.Nat as N

-- import qualified Data.Fin as F
-- import qualified Data.Fin.Enum as E

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

{-
-- inspection testing isn't smart enough here.

lhsEnum :: Ordering -> F.Fin N.Nat3
lhsEnum = E.gfrom

rhsEnum :: Ordering -> F.Fin N.Nat3
rhsEnum LT = F.Z
rhsEnum EQ = F.S F.Z
rhsEnum GT = F.S (F.S F.Z)

inspect $  'lhsEnum ==- 'rhsEnum
-}

-------------------------------------------------------------------------------
-- Main to make GHC happy
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
