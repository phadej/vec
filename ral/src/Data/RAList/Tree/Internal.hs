{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE CPP               #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
module Data.RAList.Tree.Internal (
    Leaf (..),
    Node (..),
    Dir (..),
    -- * Tree class
    -- | TODO move to private module so new instances cannot be defined
    IsTree (..),
    Size,
    Offset,
    ) where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Maybe (..), Num (..), Ord (..),
       Show, div, otherwise, seq, (&&), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Data.Hashable       (Hashable (..))
import Data.Monoid         (Monoid (..))
import Data.Semigroup      (Semigroup (..))

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

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | A 'Leaf' is isomorphic to 'Identity', but we reimplement it here
-- to have domain specific type. The short constructor name is a bonus.
newtype Leaf a = Lf a
  deriving (Eq, Ord, Show, Functor, I.Traversable)

-- | 'Node' is a product of two @f@. This way we can form a perfect binary tree.
data Node f a = Nd (f a) (f a)
  deriving (Eq, Ord, Show, Functor, I.Traversable)

-- | Direction in 'Node'.
data Dir a = L a | R a
  deriving (Eq, Ord, Show, Functor, I.Foldable, I.Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

-- These instances are manually implemented, because we can have efficient
-- foldr and foldl
instance I.Foldable Leaf where
    foldMap f (Lf x) = f x
    foldr f z (Lf x) = f x z
    foldl f z (Lf x) = f z x
    foldr' f z (Lf x) = f x z
    foldl' f z (Lf x) = f z x

#if MIN_VERSION_base(4,8,0)
    length _ = 1
    null _ = False
#endif

instance I.Foldable f => I.Foldable (Node f) where
    foldMap f (Nd x y) = mappend (I.foldMap f x) (I.foldMap f y)

    foldr f z (Nd x y) = I.foldr f (I.foldr f z y) x
    foldl f z (Nd x y) = I.foldl f (I.foldl f z x) y

    foldr' f z (Nd x y) = let !acc = I.foldr' f z y in I.foldr' f acc x
    foldl' f z (Nd x y) = let !acc = I.foldl' f z x in I.foldl' f acc y

#if MIN_VERSION_base(4,8,0)
    length (Nd x y) = I.length x + I.length y
    null (Nd x y)   = I.null x && I.null y
#endif

#ifdef MIN_VERSION_semigroupoids
instance I.Foldable1 Leaf where
    foldMap1 f (Lf x) = f x

instance I.Traversable1 Leaf where
    traverse1 f (Lf x) = Lf <$> f x

instance I.Foldable1 f => I.Foldable1 (Node f) where
    foldMap1 f (Nd x y) = I.foldMap1 f x <> I.foldMap1 f y

instance I.Traversable1 f => I.Traversable1 (Node f) where
    traverse1 f (Nd x y) = Nd <$> I.traverse1 f x <.> I.traverse1 f y
#endif

instance NFData a => NFData (Leaf a) where
    rnf (Lf a) = rnf a

instance NFData (f a) => NFData (Node f a) where
    rnf (Nd x y) = rnf x `seq` rnf y

instance Hashable a => Hashable (Leaf a) where
    hashWithSalt salt (Lf x) = hashWithSalt salt x

instance Hashable (f a) => Hashable (Node f a)  where
    hashWithSalt salt (Nd x y) = salt
        `hashWithSalt` x
        `hashWithSalt` y

#ifdef MIN_VERSION_distributive
instance I.Distributive Leaf where
    distribute xs = Lf (fmap (\(Lf x) -> x) xs)

instance I.Distributive f => I.Distributive (Node f) where
    distribute xs = Nd
        (I.distribute (fmap (\(Nd x _) -> x) xs))
        (I.distribute (fmap (\(Nd _ y) -> y) xs))

#ifdef MIN_VERSION_adjunctions
instance I.Representable Leaf where
    type Rep Leaf = ()
    index (Lf x) _ = x
    tabulate f     = Lf (f ())

instance I.Representable f => I.Representable (Node f) where
    type Rep (Node f) = Dir (I.Rep f)

    index (Nd x _) (L i) = I.index x i
    index (Nd _ y) (R j) = I.index y j

    tabulate f = Nd (I.tabulate (f . L)) (I.tabulate (f . R))
#endif
#endif

-------------------------------------------------------------------------------
-- IsLeaf
-------------------------------------------------------------------------------

-- | Size of a tree.
type Size = Int
type Offset = Int

class (
#ifdef MIN_VERSION_semigroupoids
    I.Traversable1 t
#else
    I.Traversable t
#endif
    ) => IsTree t where
    -- indexing
    safeIndex :: Size -> t a -> Int -> Maybe a

    head :: t a -> a
    last :: t a -> a

    -- folding

    ifoldr :: Offset -> Size
           -> (Int -> a -> b -> b) -> b -> t a -> b

    ifoldMap1 :: Semigroup s => Offset -> Size
              -> (Int -> a -> s) -> t a -> s

    foldr1Map  :: (        a -> b -> b) -> (a -> b) -> t a -> b
    ifoldr1Map :: Offset -> Size
               -> (Int ->  a -> b -> b) -> (Int -> a -> b) -> t a -> b

    -- mapping

    adjust :: Size -> Int -> (a -> a) -> t a -> t a

    itraverse
        :: Applicative f
        => Offset
        -> Size
        -> (Int -> a -> f b) -> t a -> f (t b)

#ifdef MIN_VERSION_semigroupoids
    traverse1  :: Apply f => (a -> f b) -> t a -> f (t b)
    itraverse1 :: Apply f => Offset -> Size -> (Int -> a -> f b) -> t a -> f (t b)
#endif

-------------------------------------------------------------------------------
-- IsTree Leaf
-------------------------------------------------------------------------------

instance IsTree Leaf where
    -- indexing
    safeIndex _ (Lf x) 0 = Just x
    safeIndex  _ _     _ = Nothing

    head (Lf x) = x
    last = head


    -- folding
    foldr1Map       _ z (Lf x) = z x

    ifoldr     !o _ f z (Lf x) = f o x z
    ifoldMap1  !o _ f   (Lf x) = f o x
    ifoldr1Map !o _ _ z (Lf x) = z o x

    -- mapping
    adjust _ !i f (Lf x)
        | 0 == i    = Lf (f x)
        | otherwise = Lf x

    itraverse !o _ f (Lf x) = fmap Lf (f o x)

#ifdef MIN_VERSION_semigroupoids
    traverse1       f (Lf x) = fmap Lf (f x)
    itraverse1 !o _ f (Lf x) = fmap Lf (f o x)
#endif

-------------------------------------------------------------------------------
-- IsTree Node
-------------------------------------------------------------------------------

instance IsTree f => IsTree (Node f) where
    -- indexing

    safeIndex s (Nd x y) i
        | i < s2    = safeIndex s2 x i
        | otherwise = safeIndex s2 y (i - s2)
      where
        s2 = s `div` 2

    head (Nd x _) = head x
    last (Nd _ y) = last y

    -- folding

    foldr1Map f z (Nd x y) = I.foldr f (foldr1Map f z y) x

    ifoldr1Map !o !s f z (Nd x y) = ifoldr o s2 f (ifoldr1Map (o + s2) s2 f z y) x
      where
        s2 = s `div` 2

    ifoldr !o !s f z (Nd x y) = ifoldr o s2 f (ifoldr (o + s2) s2 f z y) x
      where
        s2 = s `div` 2

    ifoldMap1 !o !s f (Nd x y) = ifoldMap1 o s2 f x <> ifoldMap1 (o + s2) s2 f y
      where
        s2 = s `div` 2

    -- mapping

    adjust s i f nd@(Nd x y)
        | i < s2    = Nd (adjust s2 i f x) y
        | i < s     = Nd x (adjust s2 (i - s2) f y)
        | otherwise = nd
      where
        s2 = s `div` 2

    itraverse !o !s f (Nd x y) = Nd
        <$> itraverse o        s2 f x
        <*> itraverse (o + s2) s2 f y
      where
        s2 = s `div` 2

#ifdef MIN_VERSION_semigroupoids
    traverse1 f (Nd x y) = Nd <$> traverse1 f x <.> traverse1 f y

    itraverse1 !o !s f (Nd x y) = Nd
        <$> itraverse1 o        s2 f x
        <.> itraverse1 (o + s2) s2 f y
      where
        s2 = s `div` 2
#endif

