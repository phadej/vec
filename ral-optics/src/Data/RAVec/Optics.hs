{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.Optics (
    -- * Indexing
    ix,
    ) where

import Control.Applicative        ((<$>))
import Data.Bin.Pos               (Pos (..))
import Data.BinP.PosP             (PosP (..), PosP' (..))
import Data.RAVec.NonEmpty        (NERAVec (..), NERAVec' (..))
import Data.RAVec.NonEmpty.Optics ()
import Data.RAVec.Tree            (Tree (..))
import Data.Wrd                   (Wrd (..))
import Prelude                    (Functor, (.))

import qualified Optics.Core as L

import Data.RAVec

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
-- >>> let Just ral = fromList "xyz" :: Maybe (RAVec B.Bin3 Char)
-- >>> set (ix maxBound) 'Z' ral
-- NonEmpty (NE (Cons1 (Leaf 'x') (Last (Node (Leaf 'y') (Leaf 'Z')))))
ix :: Pos b -> L.Lens' (RAVec b a) a
ix i = L.lensVL (ixVL i)

ixVL :: Functor f => Pos b -> LensLikeVL' f (RAVec b a) a
ixVL (Pos (PosP n)) f (NonEmpty (NE x)) = NonEmpty . NE <$> ixNEVL n f x

ixNEVL :: Functor f => PosP' n b -> LensLikeVL' f (NERAVec' n b a) a
ixNEVL (AtEnd i)  f (Last  t)   = Last <$> treeIxVL i f t
ixNEVL (There0 i) f (Cons0   r) = Cons0 <$> ixNEVL i f r
ixNEVL (There1 i) f (Cons1 t r) = (t `Cons1`) <$> ixNEVL i f r
ixNEVL (Here i)   f (Cons1 t r) = (`Cons1` r) <$> treeIxVL i f t

treeIxVL :: Functor f => Wrd n -> LensLikeVL' f (Tree n a) a
treeIxVL WE      f (Leaf x)   = Leaf <$> f x
treeIxVL (W0 is) f (Node x y) = (`Node` y) <$> treeIxVL is f x
treeIxVL (W1 is) f (Node x y) = (x `Node`) <$> treeIxVL is f y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.FunctorWithIndex (Pos b) (RAVec b) where
    imap = imap

instance L.FoldableWithIndex (Pos b) (RAVec b) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.TraversableWithIndex (Pos b) (RAVec b) where
    itraverse = itraverse

instance L.Each (Pos n) (RAVec n a) (RAVec n b) a b where

type instance L.Index   (RAVec n a) = Pos n
type instance L.IxValue (RAVec n a) = a

instance L.Ixed (RAVec b a) where
    type IxKind (RAVec b a) = L.A_Lens
    ix = ix
