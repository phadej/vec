{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.RAVec.NonEmpty.Optics.Internal where

import Control.Applicative ((<$>))
import Data.BinP.PosP      (PosP (..), PosP' (..))
import Data.RAVec.Tree     (Tree (..))
import Data.Wrd            (Wrd (..))
import Prelude             (Functor)

import Data.RAVec.NonEmpty

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

ixVL :: Functor f => PosP b -> LensLikeVL' f (NERAVec b a) a
ixVL (PosP i) f (NE xs) = NE <$> ixVL' i f xs

ixVL' :: Functor f => PosP' n b -> LensLikeVL' f (NERAVec' n b a) a
ixVL' (AtEnd i)  f (Last  t)   = Last <$> treeIxVL i f t
ixVL' (There0 i) f (Cons0   r) = Cons0 <$> ixVL' i f r
ixVL' (There1 i) f (Cons1 t r) = (t `Cons1`) <$> ixVL' i f r
ixVL' (Here i)   f (Cons1 t r) = (`Cons1` r) <$> treeIxVL i f t

treeIxVL :: Functor f => Wrd n -> LensLikeVL' f (Tree n a) a
treeIxVL WE      f (Leaf x)   = Leaf <$> f x
treeIxVL (W0 is) f (Node x y) = (`Node` y) <$> treeIxVL is f x
treeIxVL (W1 is) f (Node x y) = (x `Node`) <$> treeIxVL is f y
