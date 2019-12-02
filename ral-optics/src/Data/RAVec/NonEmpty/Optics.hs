{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.NonEmpty.Optics (
    -- * Indexing
    ix, ix',
    ) where

import Control.Applicative ((<$>))
import Data.BinP.PosP      (PosP (..), PosP' (..))
import Data.RAVec.Tree     (Tree (..))
import Data.Wrd            (Wrd (..))
import Prelude             (Functor)

import qualified Optics.Core as L

import Data.RAVec.NonEmpty

-- $setup
-- >>> import Optics.Core (set)
-- >>> import Prelude
-- >>> import qualified Data.Type.Bin as B

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: PosP b -> L.Lens' (NERAVec b a) a
ix i = L.lensVL (ixVL i)

ix' :: PosP' n b -> L.Lens' (NERAVec' n b a) a
ix' i = L.lensVL (ixVL' i)

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

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.FunctorWithIndex (PosP b) (NERAVec b) where
    imap = imap

instance L.FunctorWithIndex (PosP' n b) (NERAVec' n b) where
    imap = imap'

instance L.FoldableWithIndex (PosP b) (NERAVec b) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.FoldableWithIndex (PosP' n b) (NERAVec' n b) where
    ifoldMap = ifoldMap'
    ifoldr   = ifoldr'

instance L.TraversableWithIndex (PosP b) (NERAVec b) where
    itraverse = itraverse

instance L.TraversableWithIndex (PosP' n b) (NERAVec' n b) where
    itraverse = itraverse'

instance L.Each (PosP n) (NERAVec n a) (NERAVec n b) a b where

instance L.Each (PosP' n m) (NERAVec' n m a) (NERAVec' n m b) a b where

type instance L.Index   (NERAVec b a) = PosP b
type instance L.IxValue (NERAVec b a) = a

type instance L.Index   (NERAVec' n b a) = PosP' n b
type instance L.IxValue (NERAVec' n b a) = a

instance L.Ixed (NERAVec b a) where
    type IxKind (NERAVec b a) = L.A_Lens
    ix = ix

instance L.Ixed (NERAVec' n b a) where
    type IxKind (NERAVec' n b a) = L.A_Lens
    ix = ix'
