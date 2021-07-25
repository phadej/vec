{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module Inspection where

import Prelude hiding (zipWith)

import Data.Fin        (Fin (..))
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty (..))
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
lhsInline :: Vec N.Nat2 Int
lhsInline = I.zipWith (+) xs ys

-- | This doesn't evaluate compile time.
lhsNormal :: Vec N.Nat2 Int
lhsNormal = L.zipWith (+) xs ys

xs :: Vec N.Nat2 Int
xs = 1 ::: 2 ::: VNil

ys :: Vec N.Nat2 Int
ys = 2 ::: 3 ::: VNil

rhsZipWith :: Vec N.Nat2 Int
rhsZipWith = 3 ::: 5 ::: VNil

inspect $ 'lhsInline === 'rhsZipWith
inspect $ 'lhsNormal =/= 'rhsZipWith

-------------------------------------------------------------------------------
-- imap
-------------------------------------------------------------------------------

lhsIMap :: Vec N.Nat2 (F.Fin N.Nat2, Char)
lhsIMap = I.imap (,) $ 'a' ::: 'b' ::: VNil

lhsIMap' :: Vec N.Nat2 (F.Fin N.Nat2, Char)
lhsIMap' = L.imap (,) $ 'a' ::: 'b' ::: VNil

rhsIMap :: Vec N.Nat2 (F.Fin N.Nat2, Char)
rhsIMap = (FZ,'a') ::: (FS FZ,'b') ::: VNil

inspect $ 'lhsIMap  === 'rhsIMap
inspect $ 'lhsIMap' =/= 'rhsIMap

-------------------------------------------------------------------------------
-- dotProduct
-------------------------------------------------------------------------------

{-
 -- TODO: for this example LHS produces better core :O
 -- though, inlining isn't done if element is Num a => a
 --
lhsDotProduct :: Vec N.Nat2 Int -> Vec N.Nat2 Int -> Int
lhsDotProduct xs ys = I.sum (I.zipWith (*) xs ys)

rhsDotProduct :: Vec N.Nat2 Int -> Vec N.Nat2 Int -> Int
rhsDotProduct (x0 ::: x1 ::: _) (y0 ::: y1 ::: _) =
    x0 * y0 + x1 * y1

inspect $ 'lhsDotProduct === 'rhsDotProduct
-}

-------------------------------------------------------------------------------
-- join
-------------------------------------------------------------------------------

lhsJoin :: Vec N.Nat2 Char
lhsJoin = I.join $ ('a' ::: 'b' ::: VNil) ::: ('c' ::: 'd' ::: VNil) ::: VNil

lhsJoin' :: Vec N.Nat2 Char
lhsJoin' = L.join $ ('a' ::: 'b' ::: VNil) ::: ('c' ::: 'd' ::: VNil) ::: VNil

rhsJoin :: Vec N.Nat2 Char
rhsJoin = 'a' ::: 'd' ::: VNil

inspect $ 'lhsJoin  === 'rhsJoin
inspect $ 'lhsJoin' =/= 'rhsJoin

-------------------------------------------------------------------------------
-- snoc
-------------------------------------------------------------------------------

lhsSnoc :: Vec N.Nat3 Char
lhsSnoc = I.snoc ('a' ::: 'b' ::: VNil) 'c'

lhsSnoc' :: Vec N.Nat3 Char
lhsSnoc' = L.snoc ('a' ::: 'b' ::: VNil) 'c'

rhsSnoc :: Vec N.Nat3 Char
rhsSnoc = 'a' ::: 'b' ::: 'c' ::: VNil

inspect $ 'lhsSnoc  === 'rhsSnoc
inspect $ 'lhsSnoc' =/= 'rhsSnoc

-------------------------------------------------------------------------------
-- reverse
-------------------------------------------------------------------------------

lhsReverse :: Vec N.Nat3 Char
lhsReverse = I.reverse $ 'c' ::: 'b' ::: 'a' ::: VNil

lhsReverse' :: Vec N.Nat3 Char
lhsReverse' = L.reverse $ 'c' ::: 'b' ::: 'a' ::: VNil

rhsReverse :: Vec N.Nat3 Char
rhsReverse = 'a' ::: 'b' ::: 'c' ::: VNil

inspect $ 'lhsReverse  === 'rhsReverse
inspect $ 'lhsReverse' =/= 'rhsReverse

-------------------------------------------------------------------------------
-- last
-------------------------------------------------------------------------------

lhsLast :: Char
lhsLast = I.last $ 'a' ::: 'b' ::: 'c' ::: VNil

lhsLast' :: Char
lhsLast' = L.last $ 'a' ::: 'b' ::: 'c' :::VNil

rhsLast :: Char
rhsLast = 'c'

inspect $ 'lhsLast === 'rhsLast
inspect $ 'lhsLast' =/= 'rhsLast

-------------------------------------------------------------------------------
-- init
-------------------------------------------------------------------------------

lhsInit :: Vec N.Nat2 Char
lhsInit = I.init $ 'a' ::: 'b' ::: 'c' ::: VNil

lhsInit' :: Vec N.Nat2 Char
lhsInit' = L.init $ 'a' ::: 'b' ::: 'c' ::: VNil

rhsInit :: Vec N.Nat2 Char
rhsInit = 'a' ::: 'b' ::: VNil

inspect $ 'lhsInit  === 'rhsInit
inspect $ 'lhsInit' =/= 'rhsInit

-------------------------------------------------------------------------------
-- toNonEmpty
-------------------------------------------------------------------------------

lhsToNonEmpty :: NonEmpty Char
lhsToNonEmpty = I.toNonEmpty $ 'a' ::: 'b' ::: 'c' ::: VNil

lhsToNonEmpty' :: NonEmpty Char
lhsToNonEmpty' = L.toNonEmpty $ 'a' ::: 'b' ::: 'c' ::: VNil

rhsToNonEmpty :: NonEmpty Char
rhsToNonEmpty = 'a' :| ['b', 'c']

inspect $ 'lhsToNonEmpty  === 'rhsToNonEmpty
inspect $ 'lhsToNonEmpty' =/= 'rhsToNonEmpty

-------------------------------------------------------------------------------
-- scanr
-------------------------------------------------------------------------------

lhsScanr :: Vec N.Nat5 Int
lhsScanr = I.scanr (-) 0 $ 1 ::: 2 ::: 3 ::: 4 ::: VNil

lhsScanr' :: Vec N.Nat5 Int
lhsScanr' = L.scanr (-) 0 $ 1 ::: 2 ::: 3 ::: 4 ::: VNil

rhsScanr :: Vec N.Nat5 Int
rhsScanr = (-2) ::: 3 ::: (-1) ::: 4 ::: 0 ::: VNil

inspect $ 'lhsScanr  === 'rhsScanr
inspect $ 'lhsScanr' =/= 'rhsScanr
