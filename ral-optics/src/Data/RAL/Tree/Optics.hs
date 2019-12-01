{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAL.Tree.Optics (
    -- * Indexing
    ix,
    ) where

import Control.Applicative ((<$>))
import Data.Wid            (Wid (..))
import Prelude             (Functor)

import qualified Optics.Core as L

import Data.RAL.Tree

-- $setup
-- >>> import Optics.Core (set)
-- >>> import Prelude

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> let tree = Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- >>> set (ix (W1 $ W0 WE)) 'z' tree
-- Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'z') (Leaf 'd'))
--
ix :: Wid n -> L.Lens' (Tree n a) a
ix i = L.lensVL (ixVL i)

ixVL :: Functor f => Wid n -> LensLikeVL' f (Tree n a) a
ixVL WE      f (Leaf x)   = Leaf <$> f x
ixVL (W0 is) f (Node x y) = (`Node` y) <$> ixVL is f x
ixVL (W1 is) f (Node x y) = (x `Node`) <$> ixVL is f y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.FunctorWithIndex (Wid n) (Tree n) where
    imap = imap

instance L.FoldableWithIndex (Wid n) (Tree n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.TraversableWithIndex (Wid n) (Tree n) where
    itraverse = itraverse

instance L.Each (Wid n) (Tree n a) (Tree n b) a b where

type instance L.Index (Tree n a)   = Wid n
type instance L.IxValue (Tree n a) = a

instance L.Ixed (Tree n a) where
    type IxKind (Tree n a) = L.A_Lens
    ix = ix
