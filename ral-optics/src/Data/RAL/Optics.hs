{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAL.Optics (
    -- * Indexing
    ix,
    ixNE,
    ) where

import Control.Applicative ((<$>))
import Data.Bin.Pos        (Pos (..), PosN (..), PosN' (..))
import Prelude             (Functor)
import Data.Wid            (Wid (..))

import qualified Optics.Core          as L

import Data.RAL
import Data.RAL.Tree (Tree (..))

-- $setup
-- >>> import Optics.Core (set)
-- >>> import Prelude
-- >>> import qualified Data.Type.Bin as B

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> let Just ral = fromList "xyz" :: Maybe (RAL B.Bin3 Char)
-- >>> set (ix maxBound) 'Z' ral
-- NonEmpty (Cons1 (Leaf 'x') (Last (Node (Leaf 'y') (Leaf 'Z'))))
ix :: Pos b -> L.Lens' (RAL b a) a
ix i = L.lensVL (ixVL i)

ixVL :: Functor f => Pos b -> LensLikeVL' f (RAL b a) a
ixVL (Pos (PosN n)) f (NonEmpty x) = NonEmpty <$> ixNEVL n f x

ixNE :: PosN' n b -> L.Lens' (NERAL n b a) a
ixNE i = L.lensVL (ixNEVL i)

ixNEVL :: Functor f => PosN' n b -> LensLikeVL' f (NERAL n b a) a
ixNEVL (AtEnd i)  f (Last  t)   = Last <$> treeIxVL i f t
ixNEVL (There0 i) f (Cons0   r) = Cons0 <$> ixNEVL i f r
ixNEVL (There1 i) f (Cons1 t r) = (t `Cons1`) <$> ixNEVL i f r
ixNEVL (Here i)   f (Cons1 t r) = (`Cons1` r) <$> treeIxVL i f t

treeIxVL :: Functor f => Wid n -> LensLikeVL' f (Tree n a) a
treeIxVL WE      f (Leaf x)   = Leaf <$> f x
treeIxVL (W0 is) f (Node x y) = (`Node` y) <$> treeIxVL is f x
treeIxVL (W1 is) f (Node x y) = (x `Node`) <$> treeIxVL is f y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.FunctorWithIndex (Pos b) (RAL b) where
    imap = imap

instance L.FunctorWithIndex (PosN' n b) (NERAL n b) where
    imap = imapNE

instance L.FoldableWithIndex (Pos b) (RAL b) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.FoldableWithIndex (PosN' n b) (NERAL n b) where
    ifoldMap = ifoldMapNE
    ifoldr   = ifoldrNE

instance L.TraversableWithIndex (Pos b) (RAL b) where
    itraverse = itraverse

instance L.TraversableWithIndex (PosN' n b) (NERAL n b) where
    itraverse = itraverseNE

instance L.Each (Pos n) (RAL n a) (RAL n b) a b where

instance L.Each (PosN' n m) (NERAL n m a) (NERAL n m b) a b where

type instance L.Index   (RAL n a) = Pos n
type instance L.IxValue (RAL n a) = a

type instance L.Index   (NERAL n b a) = PosN' n b
type instance L.IxValue (NERAL n b a) = a

instance L.Ixed (RAL b a) where
    type IxKind (RAL b a) = L.A_Lens
    ix = ix

instance L.Ixed (NERAL n b a) where
    type IxKind (NERAL n b a) = L.A_Lens
    ix = ixNE
