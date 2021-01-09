{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAList.NonEmpty.Lens (
    -- * Indexing
    ix,
    ) where

import Control.Applicative (Applicative (pure), (<$>))
import Prelude             (Int, Num (..), Ord (..), div, otherwise)

import qualified Control.Lens     as L
import qualified Data.RAList.Tree as Tr

import Data.RAList.NonEmpty

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: forall f a. Applicative f => Int -> L.LensLike' f (NERAList a) a
ix i0 f (NE xs) = NE <$> go 1 i0 xs where
    go :: forall t. TreeIx t => Int -> Int -> NERAList' t a -> f (NERAList' t a)
    go s i (Last  t)   = Last <$> treeIx s i f t
    go s i (Cons0   r) = Cons0 <$> go (s + s) i r
    go s i (Cons1 t r)
        | i < s     = (`Cons1` r) <$> treeIx s i f t
        | otherwise = (t `Cons1`) <$> go (s + s) (i - s) r

class TreeIx t where
    treeIx :: Applicative f => Int -> Int -> (a -> f a) -> t a -> f (t a)

instance TreeIx Tr.Leaf where
    treeIx _ 0 f (Tr.Lf x) = Tr.Lf <$> f x
    treeIx _ _ _ leaf   = pure leaf

instance TreeIx t => TreeIx (Tr.Node t) where
    treeIx s i f node@(Tr.Nd x y)
        | i < s2    = (`Tr.Nd` y) <$> treeIx s2 i        f x
        | i < s     = (x `Tr.Nd`) <$> treeIx s2 (i - s2) f x
        | otherwise = pure node
      where
        s2 = s `div` 2

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if !MIN_VERSION_lens(5,0,0)
instance L.FunctorWithIndex Int NERAList where
    imap = imap

instance L.FoldableWithIndex Int NERAList where
    ifoldMap = ifoldMap

instance L.TraversableWithIndex Int NERAList where
    itraverse = itraverse
#endif

instance L.Each (NERAList a) (NERAList b) a b

type instance L.Index (NERAList a)   = Int
type instance L.IxValue (NERAList a) = a

instance L.Ixed (NERAList a) where
    ix i = ix i
