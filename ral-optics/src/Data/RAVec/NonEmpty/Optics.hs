{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAVec.NonEmpty.Optics (
    -- * Indexing
    ix, ix',
    ) where

import Data.BinP.PosP (PosP (..), PosP' (..))
import Prelude ()

import qualified Optics.Core as L

import Data.RAVec.NonEmpty
import Data.RAVec.NonEmpty.Optics.Internal

-- $setup
-- >>> import Optics.Core (set)
-- >>> import Prelude
-- >>> import qualified Data.Type.Bin as B

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

ix :: PosP b -> L.Lens' (NERAVec b a) a
ix i = L.lensVL (ixVL i)

ix' :: PosP' n b -> L.Lens' (NERAVec' n b a) a
ix' i = L.lensVL (ixVL' i)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

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
