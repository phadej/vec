{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE Safe                   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
-- | Depth indexed perfect binary tree.
module Data.RAVec.Tree (
    Tree (..),

    -- * Construction
    singleton,

    -- * Conversions
    toList,
    reverse,

    -- * Indexing
    (!),
    tabulate,
    leftmost,
    rightmost,

    -- * Folds
    foldMap,
    foldMap1,
    ifoldMap,
    ifoldMap1,
    foldr,
    ifoldr,
    foldr1Map,
    ifoldr1Map,
    foldl,
    ifoldl,

    -- * Special folds
    length,
    null,
    sum,
    product,

    -- * Mapping
    map,
    imap,
    traverse,
    itraverse,
#ifdef MIN_VERSION_semigroupoids
    traverse1,
    itraverse1,
#endif
    itraverse_,

    -- * Zipping
    zipWith,
    izipWith,
    repeat,

    -- * Universe
    universe,

    -- * QuickCheck
    liftArbitrary,
    liftShrink,
    ) where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Num, Ord (..), Show, id, seq,
       uncurry, ($), (*), (+), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Control.Monad       (void)
import Data.Hashable       (Hashable (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Semigroup      (Semigroup (..))
import Data.Typeable       (Typeable)
import Data.Wrd            (Wrd (..))

import qualified Data.Type.Nat as N

-- instances
import qualified Data.Foldable    as I (Foldable (..))
import qualified Data.Traversable as I (Traversable (..))
import qualified Test.QuickCheck  as QC

import qualified Data.Functor.WithIndex     as WI (FunctorWithIndex (..))
import qualified Data.Foldable.WithIndex    as WI (FoldableWithIndex (..))
import qualified Data.Traversable.WithIndex as WI (TraversableWithIndex (..))

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

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Prelude (Char, not, uncurry, flip, ($), Bool (..))
-- >>> import Data.Wrd (Wrd (..))
-- >>> import qualified Data.Type.Nat as N

-------------------------------------------------------------------------------
-- Data
-------------------------------------------------------------------------------

-- | Perfectly balanced binary tree of depth @n@, with @2 ^ n@ elements.
data Tree (n :: Nat) a where
    Leaf :: a -> Tree 'Z a
    Node :: Tree n a -> Tree n a -> Tree ('S n) a
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

goLeft :: (Wrd ('S n) -> a) -> Wrd n -> a
goLeft f xs = f (W0 xs)

goRight :: (Wrd ('S n) -> a) -> Wrd n -> a
goRight f xs = f (W1 xs)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq a => Eq (Tree n a)
deriving instance Ord a => Ord (Tree n a)
deriving instance Show a => Show (Tree n a)

instance Functor (Tree n) where
    fmap = map

instance I.Foldable (Tree n) where
    foldMap = foldMap
    foldr   = foldr
    foldl   = foldl

    null   = null
    toList = toList
    length = length

instance I.Traversable (Tree n) where
    traverse = traverse

-- | @since 0.2
instance WI.FunctorWithIndex (Wrd n) (Tree n) where
    imap = imap

-- | @since 0.2
instance WI.FoldableWithIndex (Wrd n) (Tree n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

-- | @since 0.2
instance WI.TraversableWithIndex (Wrd n) (Tree n) where
    itraverse = itraverse

#ifdef MIN_VERSION_semigroupoids
instance I.Foldable1 (Tree n) where
    foldMap1 = foldMap1

instance I.Traversable1 (Tree n) where
    traverse1 = traverse1
#endif

instance NFData a => NFData (Tree n a) where
    rnf (Leaf x)   = rnf x
    rnf (Node x y) = rnf x `seq` rnf y

instance Hashable a => Hashable (Tree n a) where
    hashWithSalt salt (Leaf x) = salt
        `hashWithSalt` x
    hashWithSalt salt (Node x y) = salt
        `hashWithSalt` x
        `hashWithSalt` y

instance N.SNatI n => Applicative (Tree n) where
    pure = repeat
    (<*>) = zipWith ($)
    x <* _ = x
    _ *> x = x
    liftA2 = zipWith

-- TODO: Monad

#ifdef MIN_VERSION_distributive
instance N.SNatI n => I.Distributive (Tree n) where
    distribute f = tabulate (\k -> fmap (! k) f)

#ifdef MIN_VERSION_adjunctions
instance N.SNatI n => I.Representable (Tree n) where
    type Rep (Tree n) = Wrd n

    tabulate = tabulate
    index    = (!)
#endif
#endif

instance Semigroup a => Semigroup (Tree n a) where
    Leaf x   <> Leaf y   = Leaf (x <> y)
    Node x y <> Node u v = Node (x <> u) (y <> v)

#ifdef MIN_VERSION_semigroupoids
instance Apply (Tree n) where
    (<.>)  = zipWith ($)
    _ .> x = x
    x <. _ = x
    liftF2 = zipWith
#endif

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

-- | 'Tree' of zero depth, with single element.
--
-- >>> singleton True
-- Leaf True
singleton :: a -> Tree 'Z a
singleton = Leaf

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert 'Tree' to list.
--
-- >>> toList $ Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- "abcd"
toList :: Tree n a -> [a]
toList t = go t [] where
    go :: Tree n a -> [a] -> [a]
    go (Leaf x) = (x :)
    go (Node x y) = go x . go y

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing.
(!) :: Tree n a -> Wrd n -> a
(!) (Leaf x)   WE      = x
(!) (Node x _) (W0 is) = x ! is
(!) (Node _ y) (W1 is) = y ! is

tabulate :: forall n a. N.SNatI n => (Wrd n -> a) -> Tree n a
tabulate f = case N.snat :: N.SNat n of
    N.SZ -> Leaf (f WE)
    N.SS -> Node (tabulate (goLeft f)) (tabulate (goRight f))

leftmost :: Tree n a -> a
leftmost (Leaf a)   = a
leftmost (Node x _) = leftmost x

rightmost :: Tree n a -> a
rightmost (Leaf a)   = a
rightmost (Node _ y) = rightmost y

-------------------------------------------------------------------------------
-- Reverse
-------------------------------------------------------------------------------

-- | Reverse 'Tree'.
--
-- >>> let t = Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- >>> reverse t
-- Node (Node (Leaf 'd') (Leaf 'c')) (Node (Leaf 'b') (Leaf 'a'))
--
-- @since 0.1.1
reverse :: Tree n a -> Tree n a
reverse t@(Leaf _) = t
reverse (Node x y) = Node (reverse y) (reverse x)

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldMap :: Monoid m => (a -> m) -> Tree n a -> m
foldMap f (Leaf x)   = f x
foldMap f (Node x y) = mappend (foldMap f x) (foldMap f y)

ifoldMap :: Monoid m => (Wrd n -> a -> m) -> Tree n a -> m
ifoldMap f (Leaf x)   = f WE x
ifoldMap f (Node x y) = mappend (ifoldMap (goLeft f) x) (ifoldMap (goRight f) y)

foldMap1 :: Semigroup s => (a -> s) -> Tree n a -> s
foldMap1 f (Leaf x)   = f x
foldMap1 f (Node x y) = foldMap1 f x <> foldMap1 f y

ifoldMap1 :: Semigroup s => (Wrd n -> a -> s) -> Tree n a -> s
ifoldMap1 f (Leaf x)   = f WE x
ifoldMap1 f (Node x y) = ifoldMap1 (goLeft f) x <> ifoldMap1 (goRight f) y

-- | >>> foldr (:) [] $ Node (Leaf True) (Leaf False)
-- [True,False]
foldr :: (a -> b -> b) -> b -> Tree n a -> b
foldr f z (Leaf x)   = f x z
foldr f z (Node x y) = foldr f (foldr f z y) x

ifoldr :: (Wrd n -> a -> b -> b) -> b -> Tree n a -> b
ifoldr f z (Leaf x)   = f WE x z
ifoldr f z (Node x y) = ifoldr (goLeft f) (ifoldr (goRight f) z y) x

foldr1Map :: (a -> b -> b) -> (a -> b) -> Tree n a -> b
foldr1Map _ z (Leaf x)   = z x
foldr1Map f z (Node x y) = foldr f (foldr1Map f z y) x

ifoldr1Map :: (Wrd n -> a -> b -> b) -> (Wrd n -> a -> b) -> Tree n a -> b
ifoldr1Map _ z (Leaf x) = z WE x
ifoldr1Map f z (Node x y) = ifoldr (goLeft f) (ifoldr1Map (goRight f) (goRight z) y) x

-- | >>> foldl (flip (:)) [] $ Node (Leaf True) (Leaf False)
-- [False,True]
foldl :: (b -> a -> b) -> b -> Tree n a -> b
foldl f z (Leaf x) = f z x
foldl f z (Node x y) = foldl f (foldl f z x) y

ifoldl :: (Wrd n -> b -> a -> b) -> b -> Tree n a -> b
ifoldl f z (Leaf x)   = f WE z x
ifoldl f z (Node x y) = ifoldl (goLeft f) (ifoldl (goRight f) z x) y

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- | @since 0.1.1
null :: Tree n a -> Bool
null _ = False

-- | >>> length (universe :: Tree N.Nat3 (Wrd N.Nat3))
-- 8
--
length :: Tree n a -> Int
length = go 1 where
    go :: Int -> Tree n a -> Int
    go !acc (Leaf _)   = acc
    go  acc (Node x _) = go (2 * acc) x

-- | Non-strict 'sum'.
--
-- @since 0.1.1
sum :: Num a => Tree n a -> a
sum (Leaf a)   = a
sum (Node x y) = sum x + sum y

-- | Non-strict 'product'.
--
-- @since 0.1.1
product :: Num a => Tree n a -> a
product (Leaf a)   = a
product (Node x y) = product x * product y

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- | >>> map not $ Node (Leaf True) (Leaf False)
-- Node (Leaf False) (Leaf True)
map :: (a -> b) -> Tree n a -> Tree n b
map f (Leaf x)   = Leaf (f x)
map f (Node x y) = Node (map f x) (map f y)

-- | >>> imap (,) $ Node (Leaf True) (Leaf False)
-- Node (Leaf (0b0,True)) (Leaf (0b1,False))
imap :: (Wrd n -> a -> b) -> Tree n a -> Tree n b
imap f (Leaf x) = Leaf (f WE x)
imap f (Node x y) = Node (imap (goLeft f) x) (imap (goRight f) y)

traverse :: Applicative f => (a -> f b) -> Tree n a -> f (Tree n b)
traverse f (Leaf x)   = Leaf <$> f x
traverse f (Node x y) = Node <$> traverse f x <*> traverse f y

itraverse :: Applicative f => (Wrd n -> a -> f b) -> Tree n a -> f (Tree n b)
itraverse f (Leaf x)   = Leaf <$> f WE x
itraverse f (Node x y) = Node <$> itraverse (goLeft f) x <*> itraverse (goRight f) y

#ifdef MIN_VERSION_semigroupoids
traverse1 :: Apply f => (a -> f b) -> Tree n a -> f (Tree n b)
traverse1 f (Leaf x)   = Leaf <$> f x
traverse1 f (Node x y) = Node <$> traverse1 f x <.> traverse1 f y

itraverse1 :: Apply f => (Wrd n -> a -> f b) -> Tree n a -> f (Tree n b)
itraverse1 f (Leaf x)   = Leaf <$> f WE x
itraverse1 f (Node x y) = Node <$> itraverse1 (goLeft f) x <.> itraverse1 (goRight f) y
#endif

-- |
-- @since 0.1.1
itraverse_ :: forall n f a b. Applicative f => (Wrd n -> a -> f b) -> Tree n a -> f ()
itraverse_ f (Leaf x)   = void (f WE x)
itraverse_ f (Node x y) = itraverse_ (f . W0) x *> itraverse_ (f . W1) y

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'Vec's with a function.
zipWith ::  (a -> b -> c) -> Tree n a -> Tree n b -> Tree n c
zipWith f (Leaf x)   (Leaf y)   = Leaf (f x y)
zipWith f (Node x y) (Node u v) = Node (zipWith f x u) (zipWith f y v)

-- | Zip two 'Tree's. with a function that also takes the elements' indices.
izipWith :: (Wrd n -> a -> b -> c) -> Tree n a -> Tree n b -> Tree n c
izipWith f (Leaf x)   (Leaf y)   = Leaf (f WE x y)
izipWith f (Node x y) (Node u v) = Node (izipWith (goLeft f) x u) (izipWith (goRight f) y v)

-- | Repeat a value.
--
-- >>> repeat 'x' :: Tree N.Nat2 Char
-- Node (Node (Leaf 'x') (Leaf 'x')) (Node (Leaf 'x') (Leaf 'x'))
--
repeat :: N.SNatI n => a -> Tree n a
repeat x = N.induction1 (Leaf x) (\t -> Node t t)

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- | Get all @'Vec' n 'Bool'@ indices in @'Tree' n@.
--
-- >>> universe :: Tree N.Nat2 (Wrd N.Nat2)
-- Node (Node (Leaf 0b00) (Leaf 0b01)) (Node (Leaf 0b10) (Leaf 0b11))
--
universe :: N.SNatI n => Tree n (Wrd n)
universe = tabulate id

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance N.SNatI n => QC.Arbitrary1 (Tree n) where
    liftArbitrary = liftArbitrary
    liftShrink    = liftShrink

liftArbitrary :: forall n a. N.SNatI n => QC.Gen a -> QC.Gen (Tree n a)
liftArbitrary arb = getArb $ N.induction1 (Arb (fmap Leaf arb)) step where
    step :: Arb m a -> Arb ('S m) a
    step (Arb rec) = Arb $ Node <$> rec <*> rec

newtype Arb n a = Arb { getArb :: QC.Gen (Tree n a) }

liftShrink :: forall n a. (a -> [a]) -> Tree n a -> [Tree n a]
liftShrink shr (Leaf x)   = Leaf <$> shr x
liftShrink shr (Node l r) = uncurry Node <$> QC.liftShrink2 rec rec (l, r) where
    rec = liftShrink shr

instance (N.SNatI n, QC.Arbitrary a) => QC.Arbitrary (Tree n a) where
    arbitrary = QC.arbitrary1
    shrink    = QC.shrink1

instance QC.CoArbitrary a => QC.CoArbitrary (Tree n a) where
    coarbitrary (Leaf x)   = QC.variant (0 :: Int) . QC.coarbitrary x
    coarbitrary (Node l r) = QC.variant (1 :: Int) . QC.coarbitrary (l, r)

instance (N.SNatI n, QC.Function a) => QC.Function (Tree n a) where
    function = case N.snat :: N.SNat n of
        N.SZ -> QC.functionMap (\(Leaf x) -> x)         Leaf
        N.SS -> QC.functionMap (\(Node l r ) -> (l, r)) (uncurry Node)
