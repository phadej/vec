{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Data.RAList.NonEmpty.Internal (
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
    length,
    null,
    -- * Conversions
    toNonEmpty,
    toList,
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

import Prelude
       (Bool (..), Eq, Functor (..), Int, Maybe, Num (..), Ord (..), Show (..),
       ShowS, String, otherwise, seq, showParen, showString, ($), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Control.Exception   (ArrayException (IndexOutOfBounds), throw)
import Data.Boring         (Absurd (..))
import Data.Hashable       (Hashable (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Maybe          (fromMaybe)
import Data.Monoid         (Monoid (..))
import Data.Semigroup      (Semigroup (..))

import qualified Data.Foldable      as I (Foldable (..))
import qualified Data.List.NonEmpty as NEList
import qualified Data.Traversable   as I (Traversable (..))
import qualified Test.QuickCheck    as QC

import qualified Data.Foldable.WithIndex    as WI (FoldableWithIndex (..))
import qualified Data.Functor.WithIndex     as WI (FunctorWithIndex (..))
import qualified Data.Traversable.WithIndex as WI (TraversableWithIndex (..))

#ifdef MIN_VERSION_semigroupoids
import Data.Functor.Apply (Apply (..))

import qualified Data.Semigroup.Foldable    as I (Foldable1 (..))
import qualified Data.Semigroup.Traversable as I (Traversable1 (..))
#endif

#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup (WrappedMonoid (..))
#endif

import qualified Data.RAList.Tree.Internal as Tr

import Data.RAList.Tree (Leaf (..), Node (..))

-- $setup
-- >>> import Data.Char (toUpper)

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

-- | Non-empty random access list.
newtype NERAList a = NE (NERAList' Leaf a)
  deriving (Eq, Ord, Functor, I.Traversable)

-- | Non-empty random access list, underlying representation.
--
-- The structure doesn't need to be hidden, as polymorphic
-- recursion of 'Node's starting from 'Leaf' keeps the 'NERAList' values well-formed.
--
data NERAList' f a
    = Last (f a)
    | Cons0 (NERAList' (Node f) a)
    | Cons1 (f a) (NERAList' (Node f) a)
  deriving (Eq, Show, Functor, I.Foldable, I.Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Ord a, I.Foldable f, Eq (f a)) => Ord (NERAList' f a) where
    compare xs ys = compare (I.foldr (:) [] xs) (I.foldr (:) [] ys)

-- |
--
-- >>> I.length $ fromNonEmpty $ 'x' :| ['a' .. 'z']
-- 27
--
instance I.Foldable NERAList where
    foldMap f (NE xs) = I.foldMap f xs

#if MIN_VERSION_base(4,8,0)
    length = length
    null   = null
#endif

#ifdef MIN_VERSION_semigroupoids
instance I.Foldable1 NERAList where
    foldMap1 f (NE xs) = I.foldMap1 f xs

instance I.Foldable1 t => I.Foldable1 (NERAList' t) where
    foldMap1 f (Last  t)   = I.foldMap1 f t
    foldMap1 f (Cons0   r) = I.foldMap1 f r
    foldMap1 f (Cons1 t r) = I.foldMap1 f t <> I.foldMap1 f r

instance I.Traversable1 NERAList where
    traverse1 f (NE xs) = NE <$> I.traverse1 f xs where

instance I.Traversable1 t => I.Traversable1 (NERAList' t) where
    traverse1 f (Last  t)   = Last <$> I.traverse1 f t
    traverse1 f (Cons0   r) = Cons0 <$> I.traverse1 f r
    traverse1 f (Cons1 t r) = Cons1 <$> I.traverse1 f t <.> I.traverse1 f r
#endif

instance NFData a => NFData (NERAList a) where
    rnf (NE r) = rnf r

instance NFData (t a) => NFData (NERAList' t a) where
    rnf (Last t)    = rnf t
    rnf (Cons0   r) = rnf r
    rnf (Cons1 t r) = rnf t `seq` rnf r

instance Hashable a => Hashable (NERAList a) where
    hashWithSalt salt (NE r) = hashWithSalt salt r

instance Hashable (t a) => Hashable (NERAList' t a) where
    hashWithSalt salt (Last t)    = salt `hashWithSalt` t
    hashWithSalt salt (Cons0   r) = salt `hashWithSalt` r
    hashWithSalt salt (Cons1 t r) = salt `hashWithSalt` t `hashWithSalt` r

-- |
--
-- >>> fromNonEmpty ('a' :| "bc") <> fromNonEmpty ('x' :| "yz")
-- fromNonEmpty ('a' :| "bcxyz")
--
instance Semigroup (NERAList a) where
    NE xs <> ys = I.foldr cons ys xs

-- TODO: Applicative, Monad

#ifdef MIN_VERSION_semigroupoids
-- Apply, Bind
#endif

-- | @since 0.2
instance WI.FunctorWithIndex Int NERAList where
    imap = imap

-- | @since 0.2
instance WI.FoldableWithIndex Int NERAList where
    ifoldMap = ifoldMap
    -- ifoldr   = ifoldr -- TODO, PR welcome!

-- | @since 0.2
instance WI.TraversableWithIndex Int NERAList where
    itraverse = itraverse

-- | @since 0.2.1
instance Absurd a => Absurd (NERAList a) where
    absurd = absurd . head

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

instance Show a => Show (NERAList a) where
    showsPrec d xs = showParen (d > 10) $ showString "fromNonEmpty " . showsPrec 11 (toNonEmpty xs)

explicitShow :: Show a => NERAList a -> String
explicitShow xs = explicitShowsPrec 0 xs ""

explicitShowsPrec :: Show a => Int -> NERAList a -> ShowS
explicitShowsPrec d (NE xs) = showParen (d > 10) $ showString "NE " . showsPrec 11 xs

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

-- | Single element 'NERAList'.
singleton :: a -> NERAList a
singleton = NE . singleton'

singleton' :: a -> NERAList' Leaf a
singleton' = Last . Lf

-- | 'cons' for non-empty rals.
cons :: a -> NERAList a -> NERAList a
cons x (NE xs) = NE (consTree (Lf x) xs)

consTree :: f a -> NERAList' f a -> NERAList' f a
consTree x (Last t)    = Cons0 (Last (Nd x t))
consTree x (Cons0 r)   = Cons1 x r
consTree x (Cons1 t r) = Cons0 (consTree (Nd x t) r)

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toNonEmpty :: NERAList a -> NonEmpty a
toNonEmpty = foldr1Map NEList.cons (:|[])

toList :: NERAList a -> [a]
toList = I.foldr (:) []

-- |
--
-- >>> fromNonEmpty ('a' :| ['b'..'f'])
-- fromNonEmpty ('a' :| "bcdef")
--
-- >>> explicitShow (fromNonEmpty ('a' :| ['b'..'f']))
-- "NE (Cons0 (Cons1 (Nd (Lf 'a') (Lf 'b')) (Last (Nd (Nd (Lf 'c') (Lf 'd')) (Nd (Lf 'e') (Lf 'f'))))))"
--
fromNonEmpty :: NonEmpty a -> NERAList a
fromNonEmpty (z :| zs) = go z zs where
    go x []     = singleton x
    go x (y:ys) = cons x (go y ys)

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | List index.
--
-- >>> fromNonEmpty ('a' :| ['b'..'f']) ! 0
-- 'a'
--
-- >>> fromNonEmpty ('a' :| ['b'..'f']) ! 5
-- 'f'
--
-- >>> fromNonEmpty ('a' :| ['b'..'f']) ! 6
-- *** Exception: array index out of range: NERAList
-- ...
--
(!) :: NERAList a -> Int -> a
(!) (NE xs) i = fromMaybe (throw $ IndexOutOfBounds "NERAList") (safeIndex' xs i)

-- | safe list index.
--
-- >>> fromNonEmpty ('a' :| ['b'..'f']) !? 0
-- Just 'a'
--
-- >>> fromNonEmpty ('a' :| ['b'..'f']) !? 5
-- Just 'f'
--
-- >>> fromNonEmpty ('a' :| ['b'..'f']) !? 6
-- Nothing
--
(!?) :: NERAList a -> Int -> Maybe a
NE xs !? i = safeIndex' xs i

safeIndex' :: Tr.IsTree f => NERAList' f a -> Int -> Maybe a
safeIndex' = go 1 where
    go :: Tr.IsTree g => Int -> NERAList' g a -> Int -> Maybe a
    go !s (Last  t)   i = Tr.safeIndex s t i
    go  s (Cons0   r) i = go (s * 2) r i
    go  s (Cons1 t r) i
        | i < s         = Tr.safeIndex s t i
        | otherwise     = go (s * 2) r (i - s)

-- | First value, head of the list.
--
-- >>> head $ fromNonEmpty $ 'a' :| ['b'..'f']
-- 'a'
head :: NERAList a -> a
head (NE x) = head' x

-- | Last value of the list
--
-- >>> last $ fromNonEmpty $  'a' :| ['b'..'f']
-- 'f'
--
last :: NERAList a -> a
last (NE x) = last' x

head' :: Tr.IsTree f => NERAList' f a -> a
head' (Last t)    = Tr.head t
head' (Cons0 r)   = head' r
head' (Cons1 t _) = Tr.head t

last' :: Tr.IsTree f => NERAList' f a -> a
last' (Last t)    = Tr.last t
last' (Cons0 r)   = last' r
last' (Cons1 _ r) = last' r

length :: NERAList a -> Int
length (NE xs) = go 0 1 xs where
    go :: Int -> Int -> NERAList' n a -> Int
    go !acc s (Last  _)   = acc + s
    go  acc s (Cons0   r) = go acc       (s + s) r
    go  acc s (Cons1 _ r) = go (acc + s) (s + s) r

null :: NERAList a -> Bool
null _ = False

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldMap1 :: forall a s. Semigroup s => (a -> s) -> NERAList a -> s
foldMap1 f (NE xs) = go (\(Lf x) -> f x) xs where
    go :: (t a -> s) -> NERAList' t a -> s
    go g (Last  t)   = g t
    go g (Cons0   r) = go (\(Nd x y) -> g x <> g y) r
    go g (Cons1 t r) = g t <> go (\(Nd x y) -> g x <> g y) r

foldr1Map :: (a -> b -> b) -> (a -> b) -> NERAList a -> b
foldr1Map f z (NE xs) = foldr1Map' f z xs

foldr1Map' :: Tr.IsTree f => (a -> b -> b) -> (a -> b) -> NERAList' f a -> b
foldr1Map' f z (Last  t)   = Tr.foldr1Map f z t
foldr1Map' f z (Cons0  r)  = foldr1Map' f z r
foldr1Map' f z (Cons1 t r) = I.foldr f (foldr1Map' f z r) t

ifoldMap :: Monoid m => (Int -> a -> m) -> NERAList a -> m
#if MIN_VERSION_base(4,11,0)
ifoldMap = ifoldMap1
#else
ifoldMap f = unwrapMonoid . ifoldMap1 (\i a -> WrapMonoid (f i a))
#endif

-- |
--
-- >>> import Data.Semigroup (Min (..))
--
-- >>> ifoldMap1 (\_ x -> Min x) $ fromNonEmpty $ 5 :| [3,1,2,4]
-- Min {getMin = 1}
--
-- >>> ifoldMap1 (\i x -> Min (i + x)) $ fromNonEmpty $ 5 :| [3,1,2,4]
-- Min {getMin = 3}
--
ifoldMap1 :: forall a s. Semigroup s => (Int -> a -> s) -> NERAList a -> s
ifoldMap1 f (NE xs) = go 0 1 xs where
    go :: Tr.IsTree t => Tr.Offset -> Tr.Size -> NERAList' t a -> s
    go o s (Last t)    = Tr.ifoldMap1 o s f t
    go o s (Cons0   r) = go o (s + s) r
    go o s (Cons1 t r) = Tr.ifoldMap1 o s f t <> go (o + s) (s + s) r

ifoldr1Map :: forall a b. (Int -> a -> b -> b) -> (Int -> a -> b) -> NERAList a -> b
ifoldr1Map f z (NE xs) = go 0 1 xs where
    go :: Tr.IsTree t => Tr.Offset -> Tr.Size -> NERAList' t a -> b
    go o s (Last  t)   = Tr.ifoldr1Map o s f z t
    go o s (Cons0   r) = go o (s * 2) r
    go o s (Cons1 t r) = Tr.ifoldr o s f (go (o + s) (s + s) r) t

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- |
-- >>> map toUpper (fromNonEmpty ('a' :| ['b'..'f']))
-- fromNonEmpty ('A' :| "BCDEF")
--
map :: (a -> b) -> NERAList a -> NERAList b
map = fmap

-- |
--
-- >>> imap (,) (fromNonEmpty ('a' :| ['b'..'f']))
-- fromNonEmpty ((0,'a') :| [(1,'b'),(2,'c'),(3,'d'),(4,'e'),(5,'f')])
imap :: (Int -> a -> b) -> NERAList a -> NERAList b
imap f xs = unI (itraverse (\i x -> I (f i x)) xs)

itraverse :: forall f a b. Applicative f => (Int -> a -> f b) -> NERAList a -> f (NERAList b)
itraverse f (NE xs) = NE <$> go 0 1 xs where
    go :: Tr.IsTree t => Tr.Offset -> Tr.Size -> NERAList' t a -> f (NERAList' t b)
    go !o !s (Last  t)   = Last <$> Tr.itraverse o s f t
    go  o  s (Cons0   r) = Cons0 <$> go o (2 * s) r
    go  o  s (Cons1 t r) = Cons1
      <$> Tr.itraverse o s f t
      <*> go (o + s) (2 * s) r

#ifdef MIN_VERSION_semigroupoids
itraverse1 :: forall f a b. Apply f => (Int -> a -> f b) -> NERAList a -> f (NERAList b)
itraverse1 f (NE xs) = NE <$> go 0 1 xs where
    go :: Tr.IsTree t => Tr.Offset -> Tr.Size -> NERAList' t a -> f (NERAList' t b)
    go !o !s (Last  t)   = Last <$> Tr.itraverse1 o s f t
    go  o  s (Cons0   r) = Cons0 <$> go o (2 * s) r
    go  o  s (Cons1 t r) = Cons1
      <$> Tr.itraverse1 o s f t
      <.> go (o + s) (2 * s) r
#endif

-- | Adjust a value in the list.
--
-- >>> adjust 3 toUpper $ fromNonEmpty $ 'a' :| "bcdef"
-- fromNonEmpty ('a' :| "bcDef")
--
-- If index is out of bounds, the list is returned unmodified.
--
-- >>> adjust 10 toUpper $ fromNonEmpty $ 'a' :| "bcdef"
-- fromNonEmpty ('a' :| "bcdef")
--
-- >>> adjust (-1) toUpper $ fromNonEmpty $ 'a' :| "bcdef"
-- fromNonEmpty ('a' :| "bcdef")
--
adjust :: forall a. Int -> (a -> a) -> NERAList a -> NERAList a
adjust i _ xs | i < 0 = xs
adjust i f (NE xs) = NE (go 0 1 xs) where
    go :: Tr.IsTree t => Tr.Offset -> Tr.Size -> NERAList' t a -> NERAList' t a
    go !o !s (Last  t)   = Last (Tr.adjust s (i - o) f t)
    go  o  s (Cons0   r) = Cons0 (go o (s + s) r)
    go  o  s (Cons1 t r)
        | i - o < s = Cons1 (Tr.adjust s (i - o) f t) r
        | otherwise = Cons1 t (go (o + s) (s + s) r)

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary1 NERAList where
    liftArbitrary arb = do
        x  <- arb
        xs <- QC.liftArbitrary arb
        pure (fromNonEmpty (x :| xs))

    liftShrink shr
        = fmap (\(x,xs) -> fromNonEmpty (x:|xs))
        . QC.liftShrink2 shr (QC.liftShrink shr)
        . (\(x:|xs) -> (x,xs)) . toNonEmpty

instance QC.Arbitrary a => QC.Arbitrary (NERAList a) where
    arbitrary = QC.arbitrary1
    shrink    = QC.shrink1

instance QC.CoArbitrary a => QC.CoArbitrary (NERAList a) where
    coarbitrary xs = QC.coarbitrary (y, ys) where
        (y:|ys) = toNonEmpty xs

instance QC.Function a => QC.Function (NERAList a) where
    function = QC.functionMap (fwd . toNonEmpty) (fromNonEmpty . bwd) where
        fwd (x :| xs) = (x, xs)
        bwd (x, xs) = x :| xs

-------------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------------

newtype I a = I a
unI :: I a -> a
unI (I a) = a

instance Functor I where
    fmap f (I x) = I (f x)

instance Applicative I where
    pure        = I
    I f <*> I x = I (f x)
    _ *> x      = x
    x <* _      = x
#if MIN_VERSION_base(4,10,0)
    liftA2 f (I x) (I y) = I (f x y)
#endif

