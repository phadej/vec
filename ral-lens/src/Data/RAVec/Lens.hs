{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.Lens (
    -- * Indexing
    ix,
    ) where

import Control.Applicative ((<$>))
import Data.Bin.Pos        (Pos (..))
import Prelude ()

import qualified Control.Lens             as L
import qualified Data.RAVec.NonEmpty.Lens as NE

import Data.RAVec

-- $setup
-- >>> import Control.Lens ((^.), (&), (.~), (^?), (#))
-- >>> import Prelude
-- >>> import Data.RAVec
-- >>> import qualified Data.Type.Bin as B

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> let Just ral = fromList "xyz" :: Maybe (RAVec B.Bin3 Char)
-- >>> ral & ix maxBound .~ 'Z'
-- NonEmpty (NE (Cons1 (Leaf 'x') (Last (Node (Leaf 'y') (Leaf 'Z')))))
ix :: Pos b -> L.Lens' (RAVec b a) a
ix (Pos n) f (NonEmpty x) = NonEmpty <$> NE.ix n f x

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.Each (RAVec n a) (RAVec n b) a b where
    each = traverse

type instance L.Index   (RAVec n a) = Pos n
type instance L.IxValue (RAVec n a) = a

instance L.Ixed (RAVec b a) where
    ix i = ix i
