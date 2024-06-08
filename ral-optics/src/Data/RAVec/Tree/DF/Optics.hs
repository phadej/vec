{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.Tree.DF.Optics (
    -- * Indexing
    ix,
    ) where

import Control.Applicative ((<$>))
import Data.Wrd            (Wrd (..))
import Prelude             (Functor)

import qualified Data.Type.Nat as N
import qualified Optics.Core   as L

import Data.RAVec.Tree.DF

-- $setup
-- >>> import Optics.Core (set, (&), (.~))
-- >>> import Prelude
-- >>> import Data.RAVec.Tree.DF
-- >>> import Data.Wrd (Wrd (..))

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

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
ix i = L.lensVL (ixVL i)

ixVL :: Functor f => Wrd n -> LensLikeVL' f (Tree n a) a
ixVL WE      f (Leaf x)   = Leaf <$> f x
ixVL (W0 is) f (Node x y) = (`Node` y) <$> ixVL is f x
ixVL (W1 is) f (Node x y) = (x `Node`) <$> ixVL is f y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance N.SNatI n => L.Each (Wrd n) (Tree n a) (Tree n b) a b

type instance L.Index (Tree n a)   = Wrd n
type instance L.IxValue (Tree n a) = a

instance L.Ixed (Tree n a) where
    type IxKind (Tree n a) = L.A_Lens
    ix = ix

