{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Pull/representable @'Vec' n a = 'Fin' n -> a@.
--
-- The module tries to have same API as "Data.Vec.Lazy", missing bits:
-- @withDict@, @toPull@, @fromPull@, @traverse@ (and variants),
-- @(++)@, @concat@ and @split@.
module Data.Vec.Pull (
    Vec (..),
    -- * Construction
    empty,
    singleton,
    -- * Conversions
    toList,
    fromList,
    fromListPrefix,
    reifyList,
    -- * Indexing
    (!),
    tabulate,
    cons,
    snoc,
    head,
    tail,
    -- * Reverse
    reverse,
    -- * Folds
    foldMap,
    foldMap1,
    ifoldMap,
    ifoldMap1,
    foldr,
    ifoldr,
    foldl',
    -- * Special folds
    length,
    null,
    sum,
    product,
    -- * Mapping
    map,
    imap,
    -- * Zipping
    zipWith,
    izipWith,
    repeat,
    -- * Monadic
    bind,
    join,
    -- * Universe
    universe,
    ) where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Maybe (..), Monad (..), Num (..),
       all, const, id, maybe, ($), (.))

import Control.Applicative (Applicative (..), (<$>))
import Data.Fin            (Fin (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Proxy          (Proxy (..))
import Data.Semigroup      (Semigroup (..))
import Data.Typeable       (Typeable)

--- Instances
import qualified Data.Foldable as I (Foldable (..))

import qualified Data.Foldable.WithIndex as WI (FoldableWithIndex (..))
import qualified Data.Functor.WithIndex  as WI (FunctorWithIndex (..))

#ifdef MIN_VERSION_adjunctions
import qualified Data.Functor.Rep as I (Representable (..))
#endif

#ifdef MIN_VERSION_distributive
import Data.Distributive (Distributive (..))
#endif

#ifdef MIN_VERSION_semigroupoids
import Data.Functor.Apply (Apply (..))

import qualified Data.Functor.Bind       as I (Bind (..))
import qualified Data.Semigroup.Foldable as I (Foldable1 (..))
#endif

-- vec siblings
import qualified Data.Fin      as F
import qualified Data.Type.Nat as N

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Prelude (Char, Bool (..), not)
-- >>> import qualified Data.Vec.Lazy as L

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

-- | Easily fuseable 'Vec'.
--
-- It unpurpose don't have /bad/ (fusion-wise) instances, like 'Traversable'.
-- Generally, there aren't functions which would be __bad consumers__ or __bad producers__.
newtype Vec n a = Vec { unVec :: Fin n -> a }
  deriving (Typeable)

instance (Eq a, N.SNatI n) => Eq (Vec n a) where
    Vec v == Vec u = all (\i -> u i == v i) F.universe

instance Functor (Vec n) where
    fmap f (Vec v) = Vec (f . v)

instance N.SNatI n => I.Foldable (Vec n) where
    foldMap = foldMap

-- | @since 0.4
instance WI.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

-- | @since 0.4
instance N.SNatI n => WI.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

#ifdef MIN_VERSION_semigroupoids
instance (N.SNatI m, n ~ 'S m)  => I.Foldable1 (Vec n) where
    foldMap1 = foldMap1
#endif

instance Applicative (Vec n) where
    pure   = repeat
    (<*>)  = zipWith ($)
    _ *> x = x
    x <* _ = x
#if MIN_VERSION_base(4,10,0)
    liftA2 = zipWith
#endif

instance Monad (Vec n) where
    return = pure
    (>>=)  = bind
    _ >> x = x

#ifdef MIN_VERSION_distributive
instance Distributive (Vec n) where
    distribute = Vec . distribute . fmap unVec

#ifdef MIN_VERSION_adjunctions
instance I.Representable (Vec n) where
    type Rep (Vec n) = Fin n
    tabulate = Vec
    index    = unVec
#endif
#endif

instance Semigroup a => Semigroup (Vec n a) where
    Vec a <> Vec b = Vec (a <> b)

instance Monoid a => Monoid (Vec n a) where
    mempty = Vec mempty
    Vec a `mappend` Vec b = Vec (mappend a b)

#ifdef MIN_VERSION_semigroupoids
instance Apply (Vec n) where
    (<.>)  = zipWith ($)
    _ .> x = x
    x <. _ = x
    liftF2 = zipWith

instance I.Bind (Vec n) where
    (>>-) = bind
    join  = join
#endif

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

-- | Empty 'Vec'.
empty :: Vec 'Z a
empty = Vec F.absurd

-- | 'Vec' with exactly one element.
--
-- >>> L.fromPull $ singleton True
-- True ::: VNil
--
singleton :: a -> Vec ('S 'Z) a
singleton = Vec . const

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert 'Vec' to list.
toList :: N.SNatI n => Vec n a -> [a]
toList v = unVec v <$> F.universe

-- | Convert list @[a]@ to @'Vec' n a@.
-- Returns 'Nothing' if lengths don't match exactly.
--
-- >>> L.fromPull <$> fromList "foo" :: Maybe (L.Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> L.fromPull <$> fromList "quux" :: Maybe (L.Vec N.Nat3 Char)
-- Nothing
--
-- >>> L.fromPull <$> fromList "xy" :: Maybe (L.Vec N.Nat3 Char)
-- Nothing
--
fromList :: N.SNatI n => [a] -> Maybe (Vec n a)
fromList = getFromList (N.induction1 start step) where
    start :: FromList 'Z a
    start = FromList $ \xs -> case xs of
        []      -> Just empty
        (_ : _) -> Nothing

    step :: FromList n a -> FromList ('N.S n) a
    step (FromList f) = FromList $ \xs -> case xs of
        []        -> Nothing
        (x : xs') -> cons x <$> f xs'

newtype FromList n a = FromList { getFromList :: [a] -> Maybe (Vec n a) }

-- | Convert list @[a]@ to @'Vec' n a@.
-- Returns 'Nothing' if input list is too short.
--
-- >>> L.fromPull <$> fromListPrefix "foo" :: Maybe (L.Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> L.fromPull <$> fromListPrefix "quux" :: Maybe (L.Vec N.Nat3 Char)
-- Just ('q' ::: 'u' ::: 'u' ::: VNil)
--
-- >>> L.fromPull <$> fromListPrefix "xy" :: Maybe (L.Vec N.Nat3 Char)
-- Nothing
--
fromListPrefix :: N.SNatI n => [a] -> Maybe (Vec n a)
fromListPrefix = getFromList (N.induction1 start step) where
    start :: FromList 'Z a
    start = FromList $ \_ -> Just empty -- different than in fromList case

    step :: FromList n a -> FromList ('N.S n) a
    step (FromList f) = FromList $ \xs -> case xs of
        []       -> Nothing
        (x : xs') -> cons x <$> f xs'

-- | Reify any list @[a]@ to @'Vec' n a@.
--
-- >>> reifyList "foo" length
-- 3
reifyList :: [a] -> (forall n. N.SNatI n => Vec n a -> r) -> r
reifyList []       f = f empty
reifyList (x : xs) f = reifyList xs $ \xs' -> f (cons x xs')

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing.
(!) :: Vec n a -> Fin n -> a
(!) = unVec

-- Tabulating, inverse of '!'.
tabulate :: (Fin n -> a) -> Vec n a
tabulate = Vec

-- | Cons an element in front of a 'Vec'.
cons :: a -> Vec n a -> Vec ('S n) a
cons x (Vec v) = Vec $ \i -> case i of
    FZ   -> x
    FS j -> v j

-- | Add a single element at the end of a 'Vec'.
--
-- @since 0.2.1
snoc :: forall a n. N.SNatI n => Vec n a -> a -> Vec ('S n) a
snoc (Vec xs) x = Vec $ \i -> maybe x xs (F.isMax i)

-- | The first element of a 'Vec'.
head :: Vec ('S n) a -> a
head (Vec v) = v FZ

-- | The elements after the 'head' of a 'Vec'.
tail :: Vec ('S n) a -> Vec n a
tail (Vec v) = Vec (v . FS)

-------------------------------------------------------------------------------
-- Reverse
-------------------------------------------------------------------------------

-- | Reverse 'Vec'.
--
-- @since 0.2.1
--
reverse :: forall n a. N.SNatI n => Vec n a -> Vec n a
reverse (Vec v) = Vec (v . F.mirror)

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- | >>> L.fromPull $ map not $ L.toPull $ True L.::: False L.::: L.VNil
-- False ::: True ::: VNil
--
map :: (a -> b) -> Vec n a -> Vec n b
map f (Vec v) = Vec (f . v)

-- | >>> L.fromPull $ imap (,) $ L.toPull $ 'a' L.::: 'b' L.::: 'c' L.::: L.VNil
-- (0,'a') ::: (1,'b') ::: (2,'c') ::: VNil
--
imap :: (Fin n -> a -> b) -> Vec n a -> Vec n b
imap f (Vec v) = Vec $ \i -> f i (v i)

-------------------------------------------------------------------------------
-- Folding
-------------------------------------------------------------------------------

-- | See 'I.Foldable'.
foldMap :: (Monoid m, N.SNatI n) => (a -> m) -> Vec n a -> m
foldMap f (Vec v) = I.foldMap (f . v) F.universe

-- | See 'I.FoldableWithIndex'.
ifoldMap :: (Monoid m, N.SNatI n) => (Fin n -> a -> m) -> Vec n a -> m
ifoldMap f (Vec v) = I.foldMap (\i -> f i (v i)) F.universe

-- | See 'I.Foldable1'.
foldMap1 :: (Semigroup s, N.SNatI n) => (a -> s) -> Vec ('S n) a -> s
foldMap1 f (Vec v) = neFoldMap (f . v) F.universe1

-- | There is no type-class for this :(
ifoldMap1 :: (Semigroup s, N.SNatI n) => (Fin ('S n) -> a -> s) -> Vec ('S n) a -> s
ifoldMap1 f (Vec v) = neFoldMap (\i -> f i (v i)) F.universe1

neFoldMap :: Semigroup s => (a -> s) -> NonEmpty a -> s
neFoldMap f (z :| zs) = go z zs where
    go x []       = f x
    go x (y : ys) = f x <> go y ys

-- | Right fold.
foldr :: N.SNatI n => (a -> b -> b) -> b -> Vec n a -> b
foldr f z (Vec v) = I.foldr (\a b -> f (v a) b) z F.universe

-- | Right fold with an index.
ifoldr :: N.SNatI n => (Fin n -> a -> b -> b) -> b -> Vec n a -> b
ifoldr f z (Vec v) = I.foldr (\a b -> f a (v a) b) z F.universe

-- | Strict left fold.
foldl' :: N.SNatI n => (b -> a -> b) -> b -> Vec n a -> b
foldl' f z (Vec v) = I.foldl' (\b a -> f b (v a)) z F.universe

-- | Yield the length of a 'Vec'.
length :: forall n a. N.SNatI n => Vec n a -> Int
length _ = N.reflectToNum (Proxy :: Proxy n)

-- | Test whether a 'Vec' is empty.
null :: forall n a. N.SNatI n => Vec n a -> Bool
null _ = case N.snat :: N.SNat n of
    N.SZ -> True
    N.SS -> False

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- | Strict 'sum'.
sum :: (Num a, N.SNatI n) => Vec n a -> a
sum (Vec v) = I.foldl' (\x i -> x + v i) 0 F.universe

-- | Strict 'product'.
product :: (Num a, N.SNatI n) => Vec n a -> a
product (Vec v) = I.foldl' (\x i -> x * v i) 1 F.universe

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'Vec's with a function.
zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f (Vec xs) (Vec ys) = Vec $ \i -> f (xs i) (ys i)

-- | Zip two 'Vec's. with a function that also takes the elements' indices.
izipWith :: (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
izipWith f (Vec xs) (Vec ys) = Vec $ \i -> f i (xs i) (ys i)

-- | Repeat value
--
-- @since 0.2.1
repeat :: x -> Vec n x
repeat = Vec . pure

-------------------------------------------------------------------------------
-- Monadic
-------------------------------------------------------------------------------

-- | Monadic bind.
bind :: Vec n a -> (a -> Vec n b) -> Vec n b
bind m k = Vec $ unVec m >>= unVec . k

-- | Monadic join.
join :: Vec n (Vec n a) -> Vec n a
join (Vec v) = Vec $ \i -> unVec (v i) i

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- | Get all @'Fin' n@ in a @'Vec' n@.
--
-- >>> L.fromPull (universe :: Vec N.Nat3 (Fin N.Nat3))
-- 0 ::: 1 ::: 2 ::: VNil
universe :: N.SNatI n => Vec n (Fin n)
universe = Vec id
