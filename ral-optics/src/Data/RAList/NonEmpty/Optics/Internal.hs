{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.RAList.NonEmpty.Optics.Internal where

import Control.Applicative ((<$>))
import Prelude
       (Functor (..), Int, Num (..), Ord (..), div, otherwise)

import qualified Data.RAList.Tree as Tr

import Data.RAList.NonEmpty

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

ixVL :: forall f a. Functor f => Int -> (forall x. x -> f x) -> LensLikeVL' f (NERAList a) a
ixVL i0 point f (NE xs) = NE <$> go 1 i0 xs where
    go :: forall t. TreeIx t => Int -> Int -> NERAList' t a -> f (NERAList' t a)
    go s i (Last  t)   = Last <$> treeIx s i point f t
    go s i (Cons0   r) = Cons0 <$> go (s + s) i r
    go s i (Cons1 t r)
        | i < s     = (`Cons1` r) <$> treeIx s i point f t
        | otherwise = (t `Cons1`) <$> go (s + s) (i - s) r

class TreeIx t where
    treeIx :: Functor f => Int -> Int -> (forall x. x -> f x) -> (a -> f a) -> t a -> f (t a)

instance TreeIx Tr.Leaf where
    treeIx _ 0 _     f (Tr.Lf x) = Tr.Lf <$> f x
    treeIx _ _ point _ leaf      = point leaf

instance TreeIx t => TreeIx (Tr.Node t) where
    treeIx s i point f node@(Tr.Nd x y)
        | i < s2    = (`Tr.Nd` y) <$> treeIx s2 i        point f x
        | i < s     = (x `Tr.Nd`) <$> treeIx s2 (i - s2) point f x
        | otherwise = point node
      where
        s2 = s `div` 2
