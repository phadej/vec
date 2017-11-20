{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Main (main) where

import Prelude hiding (zipWith)

import Data.Vec.Lazy   (Vec (..))
import Test.Inspection

import qualified Data.Fin             as F
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

rhsZipWith :: Vec N.Two Int
rhsZipWith = 3 ::: 5 ::: VNil

inspect $ 'lhsInline === 'rhsZipWith
inspect $ 'lhsNormal =/= 'rhsZipWith

-------------------------------------------------------------------------------
-- imap
-------------------------------------------------------------------------------

lhsIMap :: Vec N.Two (F.Fin N.Two, Char)
lhsIMap = I.imap (,) $ 'a' ::: 'b' ::: VNil

rhsIMap :: Vec N.Two (F.Fin N.Two, Char)
rhsIMap = (F.Z,'a') ::: (F.S F.Z,'b') ::: VNil

inspect $ 'lhsIMap === 'rhsIMap

-------------------------------------------------------------------------------
-- Main to make GHC happy
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
