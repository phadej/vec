{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
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
    _Vec,
    fromListPrefix,
    reifyList,
    -- * Indexing
    (!),
    ix,
    _Cons,
    _head,
    _tail,
    head,
    tail,
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
    -- * Monadic
    bind,
    join,
    -- * Universe
    universe,
    ) where

import Prelude ()
import Prelude.Compat
       (Bool (..), Eq (..), Functor (..), Int, Maybe (..),
       Monad (..), Monoid (..), Num (..), all, const, id, ($), (.), (<$>))

import Control.Applicative (Applicative (..))
import Control.Lens        ((<&>))
import Data.Distributive   (Distributive (..))
import Data.Fin            (Fin)
import Data.Functor.Apply  (Apply (..))
import Data.Functor.Rep    (Representable (..))
import Data.Nat
import Data.Proxy          (Proxy (..))
import Data.Semigroup      (Semigroup (..))
import Data.Typeable       (Typeable)

--- Instances
import qualified Control.Lens            as I
import qualified Data.Foldable           as I (Foldable (..))
import qualified Data.Functor.Bind       as I (Bind (..))
import qualified Data.Semigroup.Foldable as I (Foldable1 (..))

import qualified Data.Fin      as F
import qualified Data.Type.Nat as N

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

instance Applicative (Vec n) where
    pure   = Vec . pure
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

instance Distributive (Vec n) where
    distribute = Vec . distribute . fmap unVec

instance Representable (Vec n) where
    type Rep (Vec n) = Fin n
    tabulate = Vec
    index    = unVec

instance Semigroup a => Semigroup (Vec n a) where
    Vec a <> Vec b = Vec (a <> b)

instance Monoid a => Monoid (Vec n a) where
    mempty = Vec mempty
    Vec a `mappend` Vec b = Vec (mappend a b)

instance Apply (Vec n) where
    (<.>)  = zipWith ($)
    _ .> x = x
    x <. _ = x

instance I.Bind (Vec n) where
    (>>-) = bind
    join  = join

instance I.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

instance N.SNatI n => I.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

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

-- | Prism from list.
_Vec :: N.SNatI n => I.Prism' [a] (Vec n a)
_Vec = I.prism' toList fromList

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
reifyList :: [a] -> (forall n. N.InlineInduction n => Vec n a -> r) -> r
reifyList []       f = f empty
reifyList (x : xs) f = reifyList xs $ \xs' -> f (cons x xs')

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing.
(!) :: Vec n a -> Fin n -> a
(!) = unVec

-- | Index lens.
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) ^. L._Pull . ix (F.S F.Z)
-- 'b'
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) & L._Pull . ix (F.S F.Z) .~ 'x'
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: Fin n -> I.Lens' (Vec n a) a
ix i f (Vec v) = f (v i) <&> \a -> Vec $ \j ->
    if i == j
    then a
    else v j

-- | Match on non-empty 'Vec'.
--
-- /Note:/ @lens@ 'I._Cons' is a 'I.Prism'.
-- In fact, @'Vec' n a@ cannot have an instance of 'I.Cons' as types don't match.
--
_Cons :: I.Iso (Vec ('S n) a) (Vec ('S n) b) (a, Vec n a) (b, Vec n b)
_Cons = I.iso (\(Vec v) -> (v F.Z, Vec (v . F.S))) (\(x, xs) -> cons x xs)

-- | Head lens. /Note:/ @lens@ 'I._head' is a 'I.Traversal''.
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) ^. L._Pull . _head
-- 'a'
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) & L._Pull . _head .~ 'x'
-- 'x' ::: 'b' ::: 'c' ::: VNil
--
_head :: I.Lens' (Vec ('S n) a) a
_head f (Vec v) = f (v F.Z) <&> \a -> Vec $ \j -> case j of
    F.Z -> a
    _   -> v j
{-# INLINE head #-}

-- | Head lens. /Note:/ @lens@ 'I._head' is a 'I.Traversal''.
_tail :: I.Lens' (Vec ('S n) a) (Vec n a)
_tail f (Vec v) = f (Vec (v . F.S)) <&> \xs -> cons (v F.Z) xs
{-# INLINE _tail #-}

cons :: a -> Vec n a -> Vec ('S n) a
cons x (Vec v) = Vec $ \i -> case i of
    F.Z   -> x
    F.S j -> v j

-- | The first element of a 'Vec'.
head :: Vec ('S n) a -> a
head (Vec v) = v F.Z

-- | The elements after the 'head' of a 'Vec'.
tail :: Vec ('S n) a -> Vec n a
tail (Vec v) = Vec (v . F.S)

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- | >>> over L._Pull (map not) (True L.::: False L.::: L.VNil)
-- False ::: True ::: VNil
--
map :: (a -> b) -> Vec n a -> Vec n b
map f (Vec v) = Vec (f . v)

-- | >>> over L._Pull (imap (,)) ('a' L.::: 'b' L.::: 'c' L.::: L.VNil)
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

-- | See 'I.Foldable1'.
foldMap1 :: (Semigroup s, N.SNatI n) => (a -> s) -> Vec ('S n) a -> s
foldMap1 f (Vec v) = I.foldMap1 (f . v) F.universe1

-- | See 'I.FoldableWithIndex'.
ifoldMap :: (Monoid m, N.SNatI n) => (Fin n -> a -> m) -> Vec n a -> m
ifoldMap f (Vec v) = I.foldMap (\i -> f i (v i)) F.universe

-- | There is no type-class for this :(
ifoldMap1 :: (Semigroup s, N.SNatI n) => (Fin ('S n) -> a -> s) -> Vec ('S n) a -> s
ifoldMap1 f (Vec v) = I.foldMap1 (\i -> f i (v i)) F.universe1

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

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Lens ((^.), (&), (.~), over)
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Prelude.Compat (Char, Bool (..), not)
-- >>> import qualified Data.Vec.Lazy as L
