{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Main (main) where

import Prelude hiding (zipWith)

import Data.Vec.Lazy   (Vec (..))
import Test.Inspection

import qualified Data.Type.Nat        as N
import qualified Data.Vec.Lazy        as L
import qualified Data.Vec.Lazy.Inline as I

-------------------------------------------------------------------------------
-- zipWith
-------------------------------------------------------------------------------

-- | This doesn't evaluate compile time.
lhsInline :: Vec N.Two Int
lhsInline = I.zipWith (+) xs ys

-- | This doesn't evaluate compile time.
lhsNormal :: Vec N.Two Int
lhsNormal = L.zipWith (+) xs ys

xs :: Vec N.Two Int
xs = 1 ::: 2 ::: VNil

ys :: Vec N.Two Int
ys = 2 ::: 3 ::: VNil

rhs :: Vec N.Two Int
rhs = 3 ::: 5 ::: VNil

inspect $ 'lhsInline === 'rhs
inspect $ 'lhsNormal =/= 'rhs

-------------------------------------------------------------------------------
-- Main to make GHC happy
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
