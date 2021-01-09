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
module Data.RAList.Internal (
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
    length,
    null,
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

import Prelude
       (Bool (..), Eq, Functor (..), Int, Maybe (..), Ord (..), Show (..),
       ShowS, String, showParen, showString, ($), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Control.Exception   (ArrayException (IndexOutOfBounds), throw)
import Data.Hashable       (Hashable (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Monoid         (Monoid (..))
import Data.Semigroup      (Semigroup (..))

import qualified Data.Foldable    as I (Foldable (..))
import qualified Data.Traversable as I (Traversable (..))
import qualified Test.QuickCheck  as QC

import qualified Data.Foldable.WithIndex    as WI (FoldableWithIndex (..))
import qualified Data.Functor.WithIndex     as WI (FunctorWithIndex (..))
import qualified Data.Traversable.WithIndex as WI (TraversableWithIndex (..))

import qualified Data.RAList.NonEmpty.Internal as NE

-- $setup
-- >>> import Data.Char (toUpper)

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

-- | Random access list.
data RAList a
    = Empty
    | NonEmpty (NE.NERAList a)
  deriving (Eq, Ord, Functor, I.Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

-- |
--
-- >>> I.length $ fromList $ ['a' .. 'z']
-- 26
--
instance I.Foldable RAList where
    foldMap _ Empty = mempty
    foldMap f (NonEmpty xs) = I.foldMap f xs

#if MIN_VERSION_base(4,8,0)
    length = length
    null   = null
#endif

instance NFData a => NFData (RAList a) where
    rnf Empty         = ()
    rnf (NonEmpty xs) = rnf xs

instance Hashable a => Hashable (RAList a) where
    hashWithSalt salt Empty        = hashWithSalt salt (0 :: Int)
    hashWithSalt salt (NonEmpty r) = hashWithSalt salt r


-- |
--
-- >>> fromList "abc" <> fromList "xyz"
-- fromList "abcxyz"
--
instance Semigroup (RAList a) where
    Empty       <> ys          = ys
    xs          <> Empty       = xs
    NonEmpty xs <> NonEmpty ys = NonEmpty (xs <> ys)

instance Monoid (RAList a) where
    mempty  = Empty
    mappend = (<>)

-- TODO: Applicative, Monad

#ifdef MIN_VERSION_semigroupoids
-- Apply, Bind
#endif

-- | @since 0.2
instance WI.FunctorWithIndex Int RAList where
    imap = imap

-- | @since 0.2
instance WI.FoldableWithIndex Int RAList where
    ifoldMap = ifoldMap
    -- ifoldr   = ifoldr -- TODO, PR welcome!

-- | @since 0.2
instance WI.TraversableWithIndex Int RAList where
    itraverse = itraverse

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

instance Show a => Show (RAList a) where
    showsPrec d xs = showParen (d > 10) $ showString "fromList " . showsPrec 11 (toList xs)

explicitShow :: Show a => RAList a -> String
explicitShow xs = explicitShowsPrec 0 xs ""

explicitShowsPrec :: Show a => Int -> RAList a -> ShowS
explicitShowsPrec _ Empty         = showString "Empty"
explicitShowsPrec d (NonEmpty xs) = showParen (d > 10) $ showString "NonEmpty " . NE.explicitShowsPrec 11 xs

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

-- | Empty 'RAList'.
--
-- >>> empty :: RAList Int
-- fromList []
--
empty :: RAList a
empty = Empty

-- | Single element 'RAList'.
singleton :: a -> RAList a
singleton = NonEmpty . NE.singleton

-- | 'cons' for non-empty rals.
cons :: a -> RAList a -> RAList a
cons x Empty         = singleton x
cons x (NonEmpty xs) = NonEmpty (NE.cons x xs)

toList :: RAList a -> [a]
toList Empty         = []
toList (NonEmpty xs) = I.foldr (:) [] xs

-- |
--
-- >>> fromList ['a' .. 'f']
-- fromList "abcdef"
--
-- >>> explicitShow $ fromList ['a' .. 'f']
-- "NonEmpty (NE (Cons0 (Cons1 (Nd (Lf 'a') (Lf 'b')) (Last (Nd (Nd (Lf 'c') (Lf 'd')) (Nd (Lf 'e') (Lf 'f')))))))"
--
fromList :: [a] -> RAList a
fromList []     = Empty
fromList (x:xs) = NonEmpty (NE.fromNonEmpty (x :| xs))

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | List index.
--
--- >>> fromList ['a'..'f'] ! 0
-- 'a'
--
-- >>> fromList ['a'..'f'] ! 5
-- 'f'
--
-- >>> fromList ['a'..'f'] ! 6
-- *** Exception: array index out of range: RAList
-- ...
--
(!) :: RAList a -> Int -> a
(!) Empty         _ = throw $ IndexOutOfBounds "RAList"
(!) (NonEmpty xs) i = xs NE.! i

-- | safe list index.
--
-- >>> fromList ['a'..'f'] !? 0
-- Just 'a'
--
-- >>> fromList ['a'..'f'] !? 5
-- Just 'f'
--
-- >>> fromList ['a'..'f'] !? 6
-- Nothing
--
(!?) :: RAList a -> Int -> Maybe a
Empty       !? _ = Nothing
NonEmpty xs !? i = xs NE.!? i

length :: RAList a -> Int
length Empty         = 0
length (NonEmpty xs) = NE.length xs

null :: RAList a -> Bool
null Empty        = True
null (NonEmpty _) = False

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

ifoldMap :: Monoid m => (Int -> a -> m) -> RAList a -> m
ifoldMap _ Empty        = mempty
ifoldMap f (NonEmpty r) = NE.ifoldMap f r

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- |
-- >>> map toUpper (fromList ['a'..'f'])
-- fromList "ABCDEF"
--
map :: (a -> b) -> RAList a -> RAList b
map = fmap

-- |
--
-- >>> imap (,) $ fromList ['a' .. 'f']
-- fromList [(0,'a'),(1,'b'),(2,'c'),(3,'d'),(4,'e'),(5,'f')]
imap :: (Int -> a -> b) -> RAList a -> RAList b
imap f xs = unI (itraverse (\i x -> I (f i x)) xs)

itraverse :: forall f a b. Applicative f => (Int -> a -> f b) -> RAList a -> f (RAList b)
itraverse _ Empty         = pure Empty
itraverse f (NonEmpty xs) = NonEmpty <$> NE.itraverse f xs

-- | Adjust a value in the list.
--
-- >>> adjust 3 toUpper $ fromList "bcdef"
-- fromList "bcdEf"
--
-- If index is out of bounds, the list is returned unmodified.
--
-- >>> adjust 10 toUpper $ fromList "bcdef"
-- fromList "bcdef"
--
-- >>> adjust (-1) toUpper $ fromList "bcdef"
-- fromList "bcdef"
--
adjust :: forall a. Int -> (a -> a) -> RAList a -> RAList a
adjust _ _ Empty         = Empty
adjust i f (NonEmpty xs) = NonEmpty (NE.adjust i f xs)

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary1 RAList where
    liftArbitrary = fmap fromList . QC.liftArbitrary
    liftShrink shr = fmap fromList . QC.liftShrink shr . toList

instance QC.Arbitrary a => QC.Arbitrary (RAList a) where
    arbitrary = QC.arbitrary1
    shrink    = QC.shrink1

instance QC.CoArbitrary a => QC.CoArbitrary (RAList a) where
    coarbitrary = QC.coarbitrary . toList

instance QC.Function a => QC.Function (RAList a) where
    function = QC.functionMap toList fromList

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

