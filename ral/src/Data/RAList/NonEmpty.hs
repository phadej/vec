{-# LANGUAGE CPP #-}
-- | Non-empty random access list.
--
-- This module is designed to imported qualifed.
--
module Data.RAList.NonEmpty (
    NERAList (..),
    NERAList' (..),
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Construction
    singleton,
    cons,
    -- * Indexing
    (!),
    (!?),
    head,
    last,
    uncons,
    tail,
    -- * Conversions
    toNonEmpty,
    fromNonEmpty,
    -- * Folding
    foldMap1,
    foldr1Map,
    ifoldMap,
    ifoldMap1,
    ifoldr1Map,
    -- * Mapping
    adjust,
    map,
    imap,
    itraverse,
#ifdef MIN_VERSION_semigroupoids
    itraverse1,
#endif
    ) where

import Prelude (snd)
import Data.RAList.NonEmpty.Internal

import Data.RAList.Tree (Leaf (..), Node (..))
import Data.RAList.Internal (RAList (..))

-- $setup
-- >>> import Prelude (($))
-- >>> import Data.List.NonEmpty (NonEmpty (..))

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | Tail of non-empty list can be empty.
--
-- >>> tail $ fromNonEmpty $ 'a' :| "bcdef"
-- fromList "bcdef"
--
tail :: NERAList a -> RAList a
tail r = snd (uncons r)

-- | 
-- >>> uncons $ fromNonEmpty $ 'a' :| "bcdef"
-- ('a',fromList "bcdef")
uncons :: NERAList a -> (a, RAList a)
uncons (NE (Last  (Lf x)))   = (x, Empty)
uncons (NE (Cons1 (Lf x) r)) = (x, NonEmpty (NE (Cons0 r)))
uncons (NE (Cons0        r)) = 
    let (Lf x, r') = unconsTree r in (x, NonEmpty (NE r'))

unconsTree :: NERAList' (Node t) a -> (t a, NERAList' t a)
unconsTree (Last  (Nd x y))   = (x, Last y)
unconsTree (Cons1 (Nd x y) r) = (x, Cons1 y (Cons0 r))
unconsTree (Cons0          r) = 
    let (Nd x y, r') = unconsTree r in (x, Cons1 y r')
