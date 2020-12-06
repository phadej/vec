{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
{-# OPTIONS_GHC -dsuppress-all #-}
module Inspection.DataFamily.SpineStrict where

import Prelude hiding (zipWith)

import Data.Fin                        (Fin (..))
import Data.Vec.DataFamily.SpineStrict (Vec (..))
import Test.Inspection

import qualified Data.Fin                        as F
import qualified Data.Type.Nat                   as N
import qualified Data.Vec.DataFamily.SpineStrict as I

-------------------------------------------------------------------------------
-- zipWith
-------------------------------------------------------------------------------

-- | This doesn't evaluate compile time.
lhsInline :: Vec N.Nat2 Int
lhsInline = I.zipWith (+) oneTwo twoThree

oneTwo :: Vec N.Nat2 Int
oneTwo = 1 ::: 2 ::: VNil

twoThree :: Vec N.Nat2 Int
twoThree = 2 ::: 3 ::: VNil

rhsZipWith :: Vec N.Nat2 Int
rhsZipWith = 3 ::: 5 ::: VNil

inspect $ 'lhsInline === 'rhsZipWith

-------------------------------------------------------------------------------
-- imap
-------------------------------------------------------------------------------

lhsIMap :: Vec N.Nat2 (F.Fin N.Nat2, Char)
lhsIMap = I.imap (,) $ 'a' ::: 'b' ::: VNil

rhsIMap :: Vec N.Nat2 (F.Fin N.Nat2, Char)
rhsIMap = (FZ,'a') ::: (FS FZ,'b') ::: VNil

inspect $ 'lhsIMap  === 'rhsIMap

-------------------------------------------------------------------------------
-- dotProduct
-------------------------------------------------------------------------------

lhsDotProduct :: Vec N.Nat2 Int -> Vec N.Nat2 Int -> Int
lhsDotProduct xs ys = I.sum (I.zipWith (*) xs ys)

rhsDotProduct :: Vec N.Nat2 Int -> Vec N.Nat2 Int -> Int
rhsDotProduct (x0 ::: x1 ::: _) (y0 ::: y1 ::: _) =
    x0 * y0 + x1 * y1

inspect $ 'lhsDotProduct === 'rhsDotProduct

-------------------------------------------------------------------------------
-- join
-------------------------------------------------------------------------------

lhsJoin :: Vec N.Nat2 Char
lhsJoin = I.join $ ('a' ::: 'b' ::: VNil) ::: ('c' ::: 'd' ::: VNil) ::: VNil

rhsJoin :: Vec N.Nat2 Char
rhsJoin = 'a' ::: 'd' ::: VNil

inspect $ 'lhsJoin  === 'rhsJoin

-------------------------------------------------------------------------------
-- snoc
-------------------------------------------------------------------------------

lhsSnoc :: Vec N.Nat3 Char
lhsSnoc = I.snoc ('a' ::: 'b' ::: VNil) 'c'

rhsSnoc :: Vec N.Nat3 Char
rhsSnoc = 'a' ::: 'b' ::: 'c' ::: VNil

inspect $ 'lhsSnoc  === 'rhsSnoc

-------------------------------------------------------------------------------
-- reverse
-------------------------------------------------------------------------------

lhsReverse :: Vec N.Nat3 Char
lhsReverse = I.reverse $ 'c' ::: 'b' ::: 'a' ::: VNil

rhsReverse :: Vec N.Nat3 Char
rhsReverse = 'a' ::: 'b' ::: 'c' ::: VNil

inspect $ 'lhsReverse  === 'rhsReverse
