{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAList.Optics (
    -- * Indexing
    ix,
    ) where

import Prelude (Int, Functor (..))

import qualified Optics.Core as L
import qualified Data.RAList.NonEmpty.Optics.Internal as NE

import Data.RAList

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: Int -> L.AffineTraversal' (RAList a) a
ix i = L.atraversalVL (ixVL i)

ixVL :: forall f a. Functor f => Int -> (forall x. x -> f x) -> NE.LensLikeVL' f (RAList a) a
ixVL _ point _ Empty        = point Empty
ixVL i point f (NonEmpty x) = fmap NonEmpty (NE.ixVL i point f x)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if !MIN_VERSION_optics_core(0,4,0)
instance L.FunctorWithIndex Int RAList where
    imap = imap

instance L.FoldableWithIndex Int RAList where
    ifoldMap = ifoldMap

instance L.TraversableWithIndex Int RAList where
    itraverse = itraverse
#endif

instance L.Each Int (RAList a) (RAList b) a b

type instance L.Index (RAList a)   = Int
type instance L.IxValue (RAList a) = a

instance L.Ixed (RAList a) where
    ix = ix
