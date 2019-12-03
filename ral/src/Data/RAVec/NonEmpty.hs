{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
-- | Non-empty length-indexed random access list.
module Data.RAVec.NonEmpty (
    -- * Random access list
    NERAVec (..),
    NERAVec' (..),

    -- * Construction
    singleton, singleton',
    cons, consTree,
    withCons, withConsTree,
    head, head',
    last, last',

    -- * Conversion
    toList, toList',
    toNonEmpty, toNonEmpty',
    reifyNonEmpty, reifyNonEmpty',

    -- * Indexing
    (!), index',
    tabulate, tabulate',

    -- * Folds
    foldMap, foldMap',
    foldMap1, foldMap1',
    ifoldMap, ifoldMap',
    ifoldMap1, ifoldMap1',
    foldr, foldr',
    ifoldr, ifoldr',
    foldr1Map, foldr1Map',
    ifoldr1Map, ifoldr1Map',

    -- * Mapping
    map, map',
    imap, imap',
    traverse, traverse',
    itraverse, itraverse',
#ifdef MIN_VERSION_semigroupoids
    traverse1, traverse1',
    itraverse1, itraverse1',
#endif

    -- * Zipping
    zipWith, zipWith',
    izipWith, izipWith',
    repeat, repeat',

    -- * Universe
    universe, universe',
    ) where

import Prelude (Bool (..), Eq (..), Functor (..), Ord (..), Show, seq, ($), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Data.Bin            (BinP (..))
import Data.BinP.PosP      (PosP (..), PosP' (..))
import Data.Coerce         (coerce)
import Data.Hashable       (Hashable (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Semigroup      (Semigroup (..))
import Data.Type.BinP      (SBinP (..), SBinPI (..))
import Data.Typeable       (Typeable)

import qualified Data.List.NonEmpty as NEList
import qualified Data.RAVec.Tree    as Tree
import qualified Data.Type.BinP     as BP
import qualified Data.Type.Nat      as N

import qualified Data.Foldable    as I (Foldable (..))
import qualified Data.Traversable as I (Traversable (..))

#ifdef MIN_VERSION_distributive
import qualified Data.Distributive as I (Distributive (..))

#ifdef MIN_VERSION_adjunctions
import qualified Data.Functor.Rep as I (Representable (..))
#endif
#endif

#ifdef MIN_VERSION_semigroupoids
import Data.Functor.Apply (Apply (..))

import qualified Data.Semigroup.Foldable    as I (Foldable1 (..))
import qualified Data.Semigroup.Traversable as I (Traversable1 (..))
#endif

import Data.RAVec.Tree (Tree (..))

-- $setup
-- >>> :set -XScopedTypeVariables -XDataKinds
-- >>> import Prelude (print, Char, Bounded (..))
-- >>> import Data.List (sort)
-- >>> import Data.Wrd (Wrd (..))
-- >>> import Data.Bin.Pos (top, pop)
-- >>> import qualified Data.Bin.Pos as P

-------------------------------------------------------------------------------
-- Random access vec
-------------------------------------------------------------------------------

-- | Non-empty random access list.
newtype NERAVec (b :: BinP) a = NE (NERAVec' 'Z b a)
  deriving (Eq, Ord, Show, Typeable)

-- | Non-empty random access list, undelying representation.
data NERAVec' (n :: Nat) (b :: BinP) a where
    Last  :: Tree n a -> NERAVec' n 'BE a
    Cons0 ::             NERAVec' ('S n) b a -> NERAVec' n ('B0 b) a
    Cons1 :: Tree n a -> NERAVec' ('S n) b a -> NERAVec' n ('B1 b) a
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq a   => Eq   (NERAVec' n b a)
deriving instance Show a => Show (NERAVec' n b a)

instance Ord a => Ord (NERAVec' n b a) where
    compare xs ys = compare (toList' xs) (toList' ys)

instance Functor (NERAVec b) where
    fmap = map

instance Functor (NERAVec' n b) where
    fmap = map'

instance I.Foldable (NERAVec b) where
    foldMap = foldMap
    foldr   = foldr

#if MIN_VERSION_base(4,8,0)
    null _ = False
#endif

instance I.Foldable (NERAVec' n b) where
    foldMap = foldMap'
    foldr   = foldr'

#if MIN_VERSION_base(4,8,0)
    null _ = False
#endif

instance I.Traversable (NERAVec b) where
    traverse = traverse

instance I.Traversable (NERAVec' n b) where
    traverse = traverse'

#ifdef MIN_VERSION_semigroupoids
instance I.Foldable1 (NERAVec b) where
    foldMap1   = foldMap1
    toNonEmpty = toNonEmpty

instance I.Foldable1 (NERAVec' n b) where
    foldMap1   = foldMap1'
    toNonEmpty = toNonEmpty'

instance I.Traversable1 (NERAVec b) where
    traverse1 = traverse1

instance I.Traversable1 (NERAVec' n b) where
    traverse1 = traverse1'
#endif

instance NFData a => NFData (NERAVec b a) where
    rnf (NE xs) = rnf xs

instance NFData a => NFData (NERAVec' n b a) where
    rnf (Last  t)   = rnf t
    rnf (Cons0   r) = rnf r
    rnf (Cons1 t r) = rnf t `seq` rnf r

instance Hashable a => Hashable (NERAVec b a) where
    hashWithSalt salt (NE xs) = hashWithSalt salt xs

instance Hashable a => Hashable (NERAVec' n b a) where
    hashWithSalt salt = hashWithSalt salt . toList'

instance SBinPI b => Applicative (NERAVec b) where
    pure   = repeat
    (<*>)  = zipWith ($)
    x <* _ = x
    _ *> x = x
#if MIN_VERSION_base(4,10,0)
    liftA2 = zipWith
#endif

instance (SBinPI b, N.SNatI n) => Applicative (NERAVec' n b) where
    pure   = repeat'
    (<*>)  = zipWith' ($)
    x <* _ = x
    _ *> x = x
#if MIN_VERSION_base(4,10,0)
    liftA2 = zipWith'
#endif

#ifdef MIN_VERSION_distributive
instance SBinPI b => I.Distributive (NERAVec b) where
    distribute f = tabulate (\k -> fmap (! k) f)

instance (SBinPI b, N.SNatI n) => I.Distributive (NERAVec' n b) where
    distribute f = tabulate' (\k -> fmap (`index'` k) f)

#ifdef MIN_VERSION_adjunctions
instance SBinPI b => I.Representable (NERAVec b) where
    type Rep (NERAVec b) = PosP b
    index    = (!)
    tabulate = tabulate

instance (SBinPI b, N.SNatI n) => I.Representable (NERAVec' n b) where
    type Rep (NERAVec' n b) = PosP' n b
    index    = index'
    tabulate = tabulate'
#endif
#endif

instance Semigroup a => Semigroup (NERAVec b a) where
    (<>) = zipWith (<>)

instance Semigroup a => Semigroup (NERAVec' n b a) where
    (<>) = zipWith' (<>)

instance (Monoid a, SBinPI b) => Monoid (NERAVec b a) where
    mempty  = repeat mempty
    mappend = zipWith mappend

instance (Monoid a, SBinPI b, N.SNatI n) => Monoid (NERAVec' n b a) where
    mempty  = repeat' mempty
    mappend = zipWith' mappend

#ifdef MIN_VERSION_semigroupoids
instance Apply (NERAVec b) where
    (<.>)  = zipWith ($)
    liftF2 = zipWith
    _ .> x = x
    x <. _ = x

instance Apply (NERAVec' n b) where
    (<.>) = zipWith' ($)
    liftF2 = zipWith'
    _ .> x = x
    x <. _ = x
#endif

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

singleton :: forall a. a -> NERAVec BP.BinP1 a
singleton = coerce (singleton' :: a -> NERAVec' 'Z BP.BinP1 a)

singleton' :: a -> NERAVec' 'Z BP.BinP1 a
singleton' = Last . Tree.singleton

-- | 'cons' for non-empty rals.
cons :: forall a b. a -> NERAVec b a -> NERAVec (BP.Succ b) a
cons x (NE xs) = NE (consTree (Leaf x) xs)

consTree :: Tree n a -> NERAVec' n b a -> NERAVec' n (BP.Succ b) a
consTree x (Last t)    = Cons0 (Last (Node x t))
consTree x (Cons0 r)   = Cons1 x r
consTree x (Cons1 t r) = Cons0 (consTree (Node x t) r)

-- | 'withCons' for non-empty rals.
withCons :: SBinPI b => a -> NERAVec b a -> (SBinPI (BP.Succ b) => NERAVec (BP.Succ b) a -> r) -> r
withCons x (NE xs) k = withConsTree sbinp (Leaf x) xs $ k . NE

withConsTree :: SBinP b -> Tree n a -> NERAVec' n b a -> (SBinPI (BP.Succ b) => NERAVec' n (BP.Succ b) a -> r) -> r
withConsTree SBE x (Last t)    k = k (Cons0 (Last (Node x t)))
withConsTree SB0 x (Cons0 r)   k = k (Cons1 x r)
withConsTree SB1 x (Cons1 t r) k = withConsTree sbinp (Node x t) r $ k . Cons0

head :: NERAVec b a -> a
head (NE x) = head' x

head' :: NERAVec' n b a -> a
head' (Last t)     = Tree.leftmost t
head' (Cons0 ral) = head' ral
head' (Cons1 t _) = Tree.leftmost t

last :: NERAVec b a -> a
last (NE x) = last' x

last' :: NERAVec' n b a -> a
last' (Last t)       = Tree.rightmost t
last' (Cons0 ral)   = head' ral
last' (Cons1 _ ral) = last' ral

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toList :: NERAVec b a -> [a]
toList (NE xs) = toList' xs

toList' :: NERAVec' n b a -> [a]
toList' = foldr' (:) []

toNonEmpty :: NERAVec b a -> NonEmpty a
toNonEmpty (NE xs) = toNonEmpty' xs

toNonEmpty' :: NERAVec' n b a -> NonEmpty a
toNonEmpty' = foldr1Map' NEList.cons (:|[])

reifyNonEmpty :: NonEmpty a -> (forall b. SBinPI b => NERAVec b a -> r) -> r
reifyNonEmpty xs k = reifyNonEmpty' xs $ k . NE

reifyNonEmpty' :: forall a r. NonEmpty a -> (forall b. SBinPI b => NERAVec' 'Z b a -> r) -> r
reifyNonEmpty' (x0 :| xs0) = go x0 xs0 where
    go :: forall k. a -> [a] -> (forall b. SBinPI b => NERAVec' 'Z b a -> k) -> k
    go x []     k = k (Last (Leaf x))
    go x (y:ys) k = go y ys $ \zs -> withConsTree sbinp (Leaf x) zs k

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

(!) :: NERAVec b a -> PosP b -> a
(!) (NE xs) (PosP p) = index' xs p

index' :: NERAVec' n b a -> PosP' n b -> a
index' (Last t)      (AtEnd i)  = t Tree.! i
index' (Cons0 ral)   (There0 i) = index' ral i
index' (Cons1 t _)   (Here i)   = t Tree.! i
index' (Cons1 _ ral) (There1 i) = index' ral i

tabulate :: SBinPI b => (PosP b -> a) -> NERAVec b a
tabulate f = NE (tabulate' (f . PosP))

tabulate' :: forall b n a. (SBinPI b, N.SNatI n) => (PosP' n b -> a) -> NERAVec' n b a
tabulate' f = case sbinp :: SBinP b of
    SBE -> Last (Tree.tabulate (f . AtEnd))
    SB0 -> Cons0 (tabulate' (f . There0))
    SB1 -> Cons1 (Tree.tabulate (f . Here)) (tabulate' (f . There1))

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldMap :: Monoid m => (a -> m) -> NERAVec b a -> m
foldMap f (NE xs) = foldMap' f xs

foldMap' :: Monoid m => (a -> m) -> NERAVec' n b a -> m
foldMap' f (Last  t)   = Tree.foldMap f t
foldMap' f (Cons0   r) = foldMap' f r
foldMap' f (Cons1 t r) = mappend (Tree.foldMap f t) (foldMap' f r)

ifoldMap :: Monoid m => (PosP b -> a -> m) -> NERAVec b a -> m
ifoldMap f (NE xs) = ifoldMap' (f . PosP) xs

ifoldMap' :: Monoid m => (PosP' n b -> a -> m) -> NERAVec' n b a -> m
ifoldMap' f (Last  t)   = Tree.ifoldMap (f . AtEnd) t
ifoldMap' f (Cons0   r) = ifoldMap' (f . There0) r
ifoldMap' f (Cons1 t r) = Tree.ifoldMap (f . Here) t `mappend` ifoldMap' (f . There1) r

foldMap1 :: Semigroup m => (a -> m) -> NERAVec b a -> m
foldMap1 f (NE xs) = foldMap1' f xs

foldMap1' :: Semigroup m => (a -> m) -> NERAVec' n b a -> m
foldMap1' f (Last  t)   = Tree.foldMap1 f t
foldMap1' f (Cons0   r) = foldMap1' f r
foldMap1' f (Cons1 t r) = Tree.foldMap1 f t <> foldMap1' f r

ifoldMap1 :: Semigroup m => (PosP b -> a -> m) -> NERAVec b a -> m
ifoldMap1 f (NE xs) = ifoldMap1' (f . PosP) xs

ifoldMap1' :: Semigroup m => (PosP' n b -> a -> m) -> NERAVec' n b a -> m
ifoldMap1' f (Last  t)   = Tree.ifoldMap1 (f . AtEnd) t
ifoldMap1' f (Cons0   r) = ifoldMap1' (f . There0) r
ifoldMap1' f (Cons1 t r) = Tree.ifoldMap1 (f . Here) t <> ifoldMap1' (f . There1) r

foldr :: (a -> b -> b) -> b -> NERAVec m a -> b
foldr f z (NE xs) = foldr' f z xs

foldr1Map :: (a -> b -> b) -> (a -> b) -> NERAVec m a -> b
foldr1Map f z (NE xs) = foldr1Map' f z xs

ifoldr1Map :: (PosP m -> a -> b -> b) -> (PosP m -> a -> b) -> NERAVec m a -> b
ifoldr1Map f z (NE xs) = ifoldr1Map' (f . PosP) (z . PosP) xs

foldr' :: (a -> b -> b) -> b -> NERAVec' n m a -> b
foldr' f z (Last  t)   = Tree.foldr f z t
foldr' f z (Cons0   r) = foldr' f z r
foldr' f z (Cons1 t r) = Tree.foldr f (foldr' f z r) t

foldr1Map' :: (a -> b -> b) -> (a -> b) -> NERAVec' n m a -> b
foldr1Map' f z (Last t)    = Tree.foldr1Map f z t
foldr1Map' f z (Cons0   r) = foldr1Map' f z r
foldr1Map' f z (Cons1 t r) = Tree.foldr f (foldr1Map' f z r) t

ifoldr1Map' :: (PosP' n m -> a -> b -> b) -> (PosP' n m -> a -> b) -> NERAVec' n m a -> b
ifoldr1Map' f z (Last t)    = Tree.ifoldr1Map (f . AtEnd) (z . AtEnd) t
ifoldr1Map' f z (Cons0   r) = ifoldr1Map' (f . There0) (z . There0) r
ifoldr1Map' f z (Cons1 t r) = Tree.ifoldr (f . Here) (ifoldr1Map' (f . There1) (z . There1) r) t

ifoldr :: (PosP m -> a -> b -> b) -> b -> NERAVec m a -> b
ifoldr  f z (NE xs) = ifoldr' (f . PosP) z xs

ifoldr' :: (PosP' n m -> a -> b -> b) -> b -> NERAVec' n m a -> b
ifoldr' f z (Last  t)   = Tree.ifoldr (f . AtEnd) z t
ifoldr' f z (Cons0   r) = ifoldr' (f . There0) z r
ifoldr' f z (Cons1 t r) = Tree.ifoldr (f . Here) (ifoldr' (f . There1) z r) t

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- TBW

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

map :: (a -> b) -> NERAVec m a -> NERAVec m b
map f (NE xs) = NE (map' f xs)

map' :: (a -> b) -> NERAVec' n m a -> NERAVec' n m b
map' f (Last   t ) = Last (Tree.map f t)
map' f (Cons0   r) = Cons0 (map' f r)
map' f (Cons1 t r) = Cons1 (Tree.map f t) (map' f r)

imap :: (PosP m -> a -> b) -> NERAVec m a -> NERAVec m b
imap f (NE xs) = NE (imap' (f . PosP) xs)

imap' :: (PosP' n m -> a -> b) -> NERAVec' n m a -> NERAVec' n m b
imap' f (Last  t)   = Last (Tree.imap (f . AtEnd) t)
imap' f (Cons0   r) = Cons0 (imap' (f . There0) r)
imap' f (Cons1 t r) = Cons1 (Tree.imap (f . Here) t) (imap' (f . There1) r)

traverse :: Applicative f => (a -> f b) -> NERAVec m a -> f (NERAVec m b)
traverse f (NE xs) = fmap NE (traverse' f xs)

traverse' :: Applicative f => (a -> f b) -> NERAVec' n m a -> f (NERAVec' n m b)
traverse' f (Last  t)   = Last <$> Tree.traverse f t
traverse' f (Cons0   r) = Cons0 <$> traverse' f r
traverse' f (Cons1 t r) = Cons1 <$> Tree.traverse f t <*> traverse' f r

itraverse :: Applicative f => (PosP m -> a -> f b) -> NERAVec m a -> f (NERAVec m b)
itraverse f (NE xs) = fmap NE (itraverse' (f . PosP) xs)

itraverse' :: Applicative f => (PosP' n m -> a -> f b) -> NERAVec' n m a -> f (NERAVec' n m b)
itraverse' f (Last  t)   = Last <$> Tree.itraverse (f . AtEnd) t
itraverse' f (Cons0   r) = Cons0 <$> itraverse' (f . There0) r
itraverse' f (Cons1 t r) = Cons1 <$> Tree.itraverse (f . Here) t <*> itraverse' (f . There1) r

#ifdef MIN_VERSION_semigroupoids
traverse1 :: Apply f => (a -> f b) -> NERAVec m a -> f (NERAVec m b)
traverse1 f (NE xs) = fmap NE (traverse1' f xs)

traverse1' :: Apply f => (a -> f b) -> NERAVec' n m a -> f (NERAVec' n m b)
traverse1' f (Last  t)   = Last <$> Tree.traverse1 f t
traverse1' f (Cons0   r) = Cons0 <$> traverse1' f r
traverse1' f (Cons1 t r) = Cons1 <$> Tree.traverse1 f t <.> traverse1' f r

itraverse1 :: Apply f => (PosP m -> a -> f b) -> NERAVec m a -> f (NERAVec m b)
itraverse1 f (NE xs) = fmap NE (itraverse1' (f . PosP) xs)

itraverse1' :: Apply f => (PosP' n m -> a -> f b) -> NERAVec' n m a -> f (NERAVec' n m b)
itraverse1' f (Last  t)   = Last <$> Tree.itraverse1 (f . AtEnd) t
itraverse1' f (Cons0   r) = Cons0 <$> itraverse1' (f . There0) r
itraverse1' f (Cons1 t r) = Cons1 <$> Tree.itraverse1 (f . Here) t <.> itraverse1' (f . There1) r
#endif

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

zipWith :: (a -> b -> c) -> NERAVec m a -> NERAVec m b -> NERAVec m c
zipWith f (NE xs) (NE ys) = NE (zipWith' f xs ys)

-- | Zip two 'NERAVec''s with a function.
zipWith' :: (a -> b -> c) -> NERAVec' n m a -> NERAVec' n m b -> NERAVec' n m c
zipWith' f (Last  t)   (Last  t')    = Last (Tree.zipWith f t t')
zipWith' f (Cons0   r) (Cons0    r') = Cons0 (zipWith' f r r')
zipWith' f (Cons1 t r) (Cons1 t' r') = Cons1 (Tree.zipWith f t t') (zipWith' f r r')

izipWith :: (PosP m -> a -> b -> c) -> NERAVec m a -> NERAVec m b -> NERAVec m c
izipWith f (NE xs) (NE ys) = NE (izipWith' (f . PosP) xs ys)

-- | Zip two 'NERAVec''s with a function which also takes 'PosP'' index.
izipWith' :: (PosP' n m -> a -> b -> c) -> NERAVec' n m a -> NERAVec' n m b -> NERAVec' n m c
izipWith' f (Last  t)   (Last  t')    = Last (Tree.izipWith (f . AtEnd) t t')
izipWith' f (Cons0   r) (Cons0    r') = Cons0 (izipWith' (f . There0) r r')
izipWith' f (Cons1 t r) (Cons1 t' r') = Cons1 (Tree.izipWith (f . Here) t t') (izipWith' (f . There1) r r')

repeat :: SBinPI b => a -> NERAVec b a
repeat = NE . repeat'

repeat' :: forall b n a. (N.SNatI n, SBinPI b) => a -> NERAVec' n b a
repeat' x = case sbinp :: SBinP b of
    SBE -> Last (Tree.repeat x)
    SB0 -> Cons0 (repeat' x)
    SB1 -> Cons1 (Tree.repeat x) (repeat' x)

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

universe :: forall b. SBinPI b => NERAVec b (PosP b)
universe = coerce (universe' :: NERAVec' 'Z b (PosP' 'Z b))

universe' :: forall n b. (N.SNatI n, SBinPI b) => NERAVec' n b (PosP' n b)
universe' = case sbinp :: SBinP b of
    SBE -> Last  (fmap AtEnd Tree.universe)
    SB0 -> Cons0 (fmap There0 universe')
    SB1 -> Cons1 (fmap Here Tree.universe) (fmap There1 universe')
