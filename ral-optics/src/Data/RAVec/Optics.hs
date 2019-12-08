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
import Data.RAVec.NonEmpty.Optics ()

import qualified Data.RAVec.NonEmpty.Optics.Internal as NE
import qualified Optics.Core                         as L

import Data.RAVec

-- $setup
-- >>> import Optics.Core (set)
-- >>> import Prelude
-- >>> import qualified Data.Type.Bin as B

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

ixVL :: Functor f => Pos b -> NE.LensLikeVL' f (RAVec b a) a
ixVL (Pos n) f (NonEmpty x) = NonEmpty <$> NE.ixVL n f x

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
