{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAList.NonEmpty.Optics (
    -- * Indexing
    ix,
    ) where

import Prelude (Int)

import qualified Optics.Core as L

import Data.RAList.NonEmpty
import Data.RAList.NonEmpty.Optics.Internal

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: Int -> L.AffineTraversal' (NERAList a) a
ix i = L.atraversalVL (ixVL i)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.Each Int (NERAList a) (NERAList b) a b

type instance L.Index (NERAList a)   = Int
type instance L.IxValue (NERAList a) = a

instance L.Ixed (NERAList a) where
    ix = ix
