{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAList.Lens (
    -- * Indexing
    ix,
    ) where

import Control.Applicative (Applicative (..), (<$>))
import Prelude             (Int)

import qualified Control.Lens              as L
import qualified Data.RAList.NonEmpty.Lens as NE

import Data.RAList

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: forall f a. Applicative f => Int -> L.LensLike' f (RAList a) a
ix _ _ Empty         = pure Empty
ix i f (NonEmpty xs) = NonEmpty <$> NE.ix i f xs

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if !MIN_VERSION_lens(5,0,0)
instance L.FunctorWithIndex Int RAList where
    imap = imap

instance L.FoldableWithIndex Int RAList where
    ifoldMap = ifoldMap

instance L.TraversableWithIndex Int RAList where
    itraverse = itraverse
#endif

instance L.Each (RAList a) (RAList b) a b

type instance L.Index (RAList a)   = Int
type instance L.IxValue (RAList a) = a

instance L.Ixed (RAList a) where
    ix i = ix i
