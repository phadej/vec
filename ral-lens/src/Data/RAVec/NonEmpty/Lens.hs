{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.NonEmpty.Lens (
    -- * Indexing
    ix, ix',
    ) where

import Control.Applicative ((<$>))
import Data.BinP.PosP      (PosP (..), PosP' (..))
import Prelude ()

import qualified Control.Lens       as L
import qualified Data.RAVec.Tree.Lens as Tree

import Data.RAVec.NonEmpty

-- $setup
-- >>> import Control.Lens ((^.), (&), (.~), (^?), (#))
-- >>> import Prelude
-- >>> import qualified Data.Type.Bin as B

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: PosP b -> L.Lens' (NERAVec b a) a
ix (PosP i) f (NE xs) = NE <$> ix' i f xs

ix' :: PosP' n b -> L.Lens' (NERAVec' n b a) a
ix' (AtEnd i)  f (Last  t)   = Last <$> Tree.ix i f t
ix' (There0 i) f (Cons0   r) = Cons0 <$> ix' i f r
ix' (There1 i) f (Cons1 t r) = (t `Cons1`) <$> ix' i f r
ix' (Here i)   f (Cons1 t r) = (`Cons1` r) <$> Tree.ix i f t

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.Each (NERAVec n a) (NERAVec n b) a b where
    each = traverse

instance L.Each (NERAVec' n m a) (NERAVec' n m b) a b where
    each = traverse'

type instance L.Index   (NERAVec b a) = PosP b
type instance L.IxValue (NERAVec b a) = a

type instance L.Index   (NERAVec' n b a) = PosP' n b
type instance L.IxValue (NERAVec' n b a) = a

instance L.Ixed (NERAVec b a) where
    ix i = ix i

instance L.Ixed (NERAVec' n b a) where
    ix i = ix' i
