{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.Tree.Lens (
    -- * Indexing
    ix,
    ) where

import Prelude ()
import Control.Applicative ((<$>))
import Data.Wrd (Wrd (..))

import qualified Control.Lens as L

import Data.RAVec.Tree

-- $setup
-- >>> import Control.Lens ((^.), (&), (.~), (^?), (#))
-- >>> import Prelude

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> let tree = Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- >>> tree & ix (W1 $ W0 WE) .~ 'z'
-- Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'z') (Leaf 'd'))
--
ix :: Wrd n -> L.Lens' (Tree n a) a
ix WE      f (Leaf x)   = Leaf <$> f x
ix (W0 is) f (Node x y) = (`Node` y) <$> ix is f x
ix (W1 is) f (Node x y) = (x `Node`) <$> ix is f y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.FunctorWithIndex (Wrd n) (Tree n) where
    imap = imap

instance L.FoldableWithIndex (Wrd n) (Tree n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr
    ifoldl   = ifoldl

instance L.TraversableWithIndex (Wrd n) (Tree n) where
    itraverse = itraverse

instance L.Each (Tree n a) (Tree n b) a b

type instance L.Index (Tree n a)   = Wrd n
type instance L.IxValue (Tree n a) = a

instance L.Ixed (Tree n a) where
    ix i = ix i
