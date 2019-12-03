-- | Random access list.
--
-- This module is designed to imported qualifed.
--
module Data.RAList (
    RAList (..),
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Construction
    empty,
    singleton,
    cons,
    -- * Indexing
    (!),
    (!?),
    uncons,
    -- * Conversions
    toList,
    fromList,
    -- * Folding
    ifoldMap,
    -- * Mapping
    adjust,
    map,
    imap,
    itraverse,
    ) where

import Prelude (Maybe (..))
import Data.RAList.Internal

import qualified Data.RAList.NonEmpty as NE

-- $setup
-- >>> import Prelude (($))

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- |
--
-- >>> uncons $ fromList []
-- Nothing
--
-- >>> uncons $ fromList "abcdef"
-- Just ('a',fromList "bcdef")
--
uncons :: RAList a -> Maybe (a, RAList a)
uncons Empty        = Nothing
uncons (NonEmpty r) = Just (NE.uncons r)
