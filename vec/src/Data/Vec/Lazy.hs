{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE Safe                   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | Lazy (in elements and spine) length-indexed list: 'Vec'.
module Data.Vec.Lazy (
    Vec (..),
    -- * Construction
    empty,
    singleton,
    withDict,
    -- * Conversions
    toPull,
    fromPull,
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
    -- * Concatenation and splitting
    (++),
    split,
    concatMap,
    concat,
    chunks,
    -- * Take and drop
    take,
    drop,
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
    traverse,
#ifdef MIN_VERSION_semigroupoids
    traverse1,
#endif
    itraverse,
    itraverse_,
    -- * Zipping
    zipWith,
    izipWith,
    repeat,
    -- * Monadic
    bind,
    join,
    -- * Universe
    universe,
    -- * VecEach
    VecEach (..),
    )  where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Maybe (..), Monad (..), Num (..),
       Ord (..), Show (..), id, seq, showParen, showString, uncurry, ($), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Control.Lens.Yocto  ((<&>))
import Data.Fin            (Fin (..))
import Data.Hashable       (Hashable (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Semigroup      (Semigroup (..))
import Data.Typeable       (Typeable)

--- Instances
import qualified Data.Foldable    as I (Foldable (..))
import qualified Data.Traversable as I (Traversable (..))
import qualified Test.QuickCheck  as QC

import qualified Data.Foldable.WithIndex    as WI (FoldableWithIndex (..))
import qualified Data.Functor.WithIndex     as WI (FunctorWithIndex (..))
import qualified Data.Traversable.WithIndex as WI (TraversableWithIndex (..))

#ifdef MIN_VERSION_adjunctions
import qualified Data.Functor.Rep as I (Representable (..))
#endif

#ifdef MIN_VERSION_distributive
import Data.Distributive (Distributive (..))
#endif

#ifdef MIN_VERSION_semigroupoids
import Data.Functor.Apply (Apply (..))

import qualified Data.Functor.Bind          as I (Bind (..))
import qualified Data.Semigroup.Foldable    as I (Foldable1 (..))
import qualified Data.Semigroup.Traversable as I (Traversable1 (..))
#endif

-- vec siblings
import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P

import qualified Data.Type.Nat.LE          as LE.ZS
import qualified Data.Type.Nat.LE.ReflStep as LE.RS

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Prelude (Char, not, uncurry)

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

infixr 5 :::

-- | Vector, i.e. length-indexed list.
data Vec (n :: Nat) a where
    VNil  :: Vec 'Z a
    (:::) :: a -> Vec n a -> Vec ('S n) a
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq a => Eq (Vec n a)
deriving instance Ord a => Ord (Vec n a)

instance Show a => Show (Vec n a) where
    showsPrec _ VNil       = showString "VNil"
    showsPrec d (x ::: xs) = showParen (d > 5)
        $ showsPrec 6 x
        . showString " ::: "
        . showsPrec 5 xs

instance Functor (Vec n) where
    fmap = map

instance I.Foldable (Vec n) where
    foldMap = foldMap

    foldr  = foldr
    foldl' = foldl'

#if MIN_VERSION_base(4,8,0)
    null    = null
    length  = length
    sum     = sum
    product = product
#endif

instance I.Traversable (Vec n) where
    traverse = traverse

-- | @since 0.4
instance WI.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

-- | @since 0.4
instance WI.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

-- | @since 0.4
instance WI.TraversableWithIndex (Fin n) (Vec n) where
    itraverse = itraverse

#ifdef MIN_VERSION_semigroupoids
instance n ~ 'S m => I.Foldable1 (Vec n) where
    foldMap1 = foldMap1

instance n ~ 'S m => I.Traversable1 (Vec n) where
    traverse1 = traverse1
#endif

instance NFData a => NFData (Vec n a) where
    rnf VNil       = ()
    rnf (x ::: xs) = rnf x `seq` rnf xs

instance Hashable a => Hashable (Vec n a) where
    hashWithSalt salt VNil = hashWithSalt salt (0 :: Int)
    hashWithSalt salt (x ::: xs) = salt
        `hashWithSalt` x
        `hashWithSalt` xs

instance N.SNatI n => Applicative (Vec n) where
    pure   = repeat
    (<*>)  = zipWith ($)
    _ *> x = x
    x <* _ = x
#if MIN_VERSION_base(4,10,0)
    liftA2 = zipWith
#endif

instance N.SNatI n => Monad (Vec n) where
    return = pure
    (>>=)  = bind
    _ >> x = x

#ifdef MIN_VERSION_distributive
instance N.SNatI n => Distributive (Vec n) where
    distribute f = tabulate (\k -> fmap (! k) f)

#ifdef MIN_VERSION_adjunctions
instance N.SNatI n => I.Representable (Vec n) where
    type Rep (Vec n) = Fin n
    tabulate = tabulate
    index    = (!)
#endif
#endif

instance Semigroup a => Semigroup (Vec n a) where
    (<>) = zipWith (<>)

instance (Monoid a, N.SNatI n) => Monoid (Vec n a) where
    mempty = pure mempty
    mappend = zipWith mappend

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
empty = VNil

-- | 'Vec' with exactly one element.
--
-- >>> singleton True
-- True ::: VNil
--
singleton :: a -> Vec ('S 'Z) a
singleton x = x ::: VNil

-- | /O(n)/. Recover 'N.SNatI' (and 'N.SNatI') dictionary from a 'Vec' value.
--
-- Example: 'N.reflect' is constrained with @'N.SNatI' n@, but if we have a
-- @'Vec' n a@, we can recover that dictionary:
--
-- >>> let f :: forall n a. Vec n a -> N.Nat; f v = withDict v (N.reflect (Proxy :: Proxy n)) in f (True ::: VNil)
-- 1
--
-- /Note:/ using 'N.SNatI' will be suboptimal, as if GHC has no
-- opportunity to optimise the code, the recusion won't be unfold.
-- How bad such code will perform? I don't know, we'll need benchmarks.
--
withDict :: Vec n a -> (N.SNatI n => r) -> r
withDict VNil       r = r
withDict (_ ::: xs) r = withDict xs r

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert to pull 'P.Vec'.
toPull :: Vec n a -> P.Vec n a
toPull VNil       = P.Vec F.absurd
toPull (x ::: xs) = P.Vec $ \n -> case n of
    FZ   -> x
    FS m -> P.unVec (toPull xs) m

-- | Convert from pull 'P.Vec'.
fromPull :: forall n a. N.SNatI n => P.Vec n a -> Vec n a
fromPull (P.Vec f) = case N.snat :: N.SNat n of
    N.SZ -> VNil
    N.SS -> f FZ ::: fromPull (P.Vec (f . FS))

-- | Convert 'Vec' to list.
--
-- >>> toList $ 'f' ::: 'o' ::: 'o' ::: VNil
-- "foo"
toList :: Vec n a -> [a]
toList VNil       = []
toList (x ::: xs) = x : toList xs

-- | Convert list @[a]@ to @'Vec' n a@.
-- Returns 'Nothing' if lengths don't match exactly.
--
-- >>> fromList "foo" :: Maybe (Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> fromList "quux" :: Maybe (Vec N.Nat3 Char)
-- Nothing
--
-- >>> fromList "xy" :: Maybe (Vec N.Nat3 Char)
-- Nothing
--
fromList :: N.SNatI n => [a] -> Maybe (Vec n a)
fromList = getFromList (N.induction1 start step) where
    start :: FromList 'Z a
    start = FromList $ \xs -> case xs of
        []      -> Just VNil
        (_ : _) -> Nothing

    step :: FromList n a -> FromList ('N.S n) a
    step (FromList f) = FromList $ \xs -> case xs of
        []       -> Nothing
        (x : xs') -> (x :::) <$> f xs'

newtype FromList n a = FromList { getFromList :: [a] -> Maybe (Vec n a) }

-- | Convert list @[a]@ to @'Vec' n a@.
-- Returns 'Nothing' if input list is too short.
--
-- >>> fromListPrefix "foo" :: Maybe (Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> fromListPrefix "quux" :: Maybe (Vec N.Nat3 Char)
-- Just ('q' ::: 'u' ::: 'u' ::: VNil)
--
-- >>> fromListPrefix "xy" :: Maybe (Vec N.Nat3 Char)
-- Nothing
--
fromListPrefix :: N.SNatI n => [a] -> Maybe (Vec n a)
fromListPrefix = getFromList (N.induction1 start step) where
    start :: FromList 'Z a
    start = FromList $ \_ -> Just VNil -- different than in fromList case

    step :: FromList n a -> FromList ('N.S n) a
    step (FromList f) = FromList $ \xs -> case xs of
        []       -> Nothing
        (x : xs') -> (x :::) <$> f xs'

-- | Reify any list @[a]@ to @'Vec' n a@.
--
-- >>> reifyList "foo" length
-- 3
reifyList :: [a] -> (forall n. N.SNatI n => Vec n a -> r) -> r
reifyList []       f = f VNil
reifyList (x : xs) f = reifyList xs $ \xs' -> f (x ::: xs')

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing.
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) ! FS FZ
-- 'b'
--
(!) :: Vec n a -> Fin n -> a
(!) (x ::: _)  FZ     = x
(!) (_ ::: xs) (FS n) = xs ! n
(!) VNil n = case n of {}

-- | Tabulating, inverse of '!'.
--
-- >>> tabulate id :: Vec N.Nat3 (Fin N.Nat3)
-- 0 ::: 1 ::: 2 ::: VNil
--
tabulate :: N.SNatI n => (Fin n -> a) -> Vec n a
tabulate = fromPull . P.tabulate

-- | Cons an element in front of a 'Vec'.
cons :: a -> Vec n a -> Vec ('S n) a
cons = (:::)

-- | Add a single element at the end of a 'Vec'.
--
-- @since 0.2.1
snoc :: Vec n a -> a -> Vec ('S n) a
snoc VNil       x = x ::: VNil
snoc (y ::: ys) x = y ::: snoc ys x

-- | The first element of a 'Vec'.
head :: Vec ('S n) a -> a
head (x ::: _) = x

-- | The elements after the 'head' of a 'Vec'.
tail :: Vec ('S n) a -> Vec n a
tail (_ ::: xs) = xs

-------------------------------------------------------------------------------
-- Reverse
-------------------------------------------------------------------------------

-- | Reverse 'Vec'.
--
-- >>> reverse ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'c' ::: 'b' ::: 'a' ::: VNil
--
-- @since 0.2.1
--
reverse :: Vec n a -> Vec n a
reverse VNil       = VNil
reverse (x ::: xs) = snoc (reverse xs) x

-------------------------------------------------------------------------------
-- Concatenation
-------------------------------------------------------------------------------

infixr 5 ++

-- | Append two 'Vec'.
--
-- >>> ('a' ::: 'b' ::: VNil) ++ ('c' ::: 'd' ::: VNil)
-- 'a' ::: 'b' ::: 'c' ::: 'd' ::: VNil
--
(++) :: Vec n a -> Vec m a -> Vec (N.Plus n m) a
VNil       ++ ys = ys
(x ::: xs) ++ ys = x ::: xs ++ ys

-- | Split vector into two parts. Inverse of '++'.
--
-- >>> split ('a' ::: 'b' ::: 'c' ::: VNil) :: (Vec N.Nat1 Char, Vec N.Nat2 Char)
-- ('a' ::: VNil,'b' ::: 'c' ::: VNil)
--
-- >>> uncurry (++) (split ('a' ::: 'b' ::: 'c' ::: VNil) :: (Vec N.Nat1 Char, Vec N.Nat2 Char))
-- 'a' ::: 'b' ::: 'c' ::: VNil
--
split :: N.SNatI n => Vec (N.Plus n m) a -> (Vec n a, Vec m a)
split = appSplit (N.induction1 start step) where
    start :: Split m 'Z a
    start = Split $ \xs -> (VNil, xs)

    step :: Split m n a -> Split m ('S n) a
    step (Split f) = Split $ \(x ::: xs) -> case f xs of
        (ys, zs) -> (x ::: ys, zs)

newtype Split m n a = Split { appSplit :: Vec (N.Plus n m) a -> (Vec n a, Vec m a) }

-- | Map over all the elements of a 'Vec' and concatenate the resulting 'Vec's.
--
-- >>> concatMap (\x -> x ::: x ::: VNil) ('a' ::: 'b' ::: VNil)
-- 'a' ::: 'a' ::: 'b' ::: 'b' ::: VNil
--
concatMap :: (a -> Vec m b) -> Vec n a -> Vec (N.Mult n m) b
concatMap _ VNil       = VNil
concatMap f (x ::: xs) = f x ++ concatMap f xs

-- | @'concatMap' 'id'@
concat :: Vec n (Vec m a) -> Vec (N.Mult n m) a
concat = concatMap id

-- | Inverse of 'concat'.
--
-- >>> chunks <$> fromListPrefix [1..] :: Maybe (Vec N.Nat2 (Vec N.Nat3 Int))
-- Just ((1 ::: 2 ::: 3 ::: VNil) ::: (4 ::: 5 ::: 6 ::: VNil) ::: VNil)
--
-- >>> let idVec x = x :: Vec N.Nat2 (Vec N.Nat3 Int)
-- >>> concat . idVec . chunks <$> fromListPrefix [1..]
-- Just (1 ::: 2 ::: 3 ::: 4 ::: 5 ::: 6 ::: VNil)
--
chunks :: (N.SNatI n, N.SNatI m) => Vec (N.Mult n m) a -> Vec n (Vec m a)
chunks = getChunks $ N.induction1 start step where
    start :: Chunks m 'Z a
    start = Chunks $ \_ -> VNil

    step :: forall m n a. N.SNatI m => Chunks m n a -> Chunks m ('S n) a
    step (Chunks go) = Chunks $ \xs ->
        let (ys, zs) = split xs :: (Vec m a, Vec (N.Mult n m) a)
        in ys ::: go zs

newtype Chunks  m n a = Chunks  { getChunks  :: Vec (N.Mult n m) a -> Vec n (Vec m a) }

-------------------------------------------------------------------------------
-- take and drop
-------------------------------------------------------------------------------

-- |
--
-- >>> let xs = 'a' ::: 'b' ::: 'c' ::: 'd' ::: 'e' ::: VNil
-- >>> take xs :: Vec N.Nat3 Char
-- 'a' ::: 'b' ::: 'c' ::: VNil
--
take :: forall n m a. (LE.ZS.LE n m) => Vec m a -> Vec n a
take = go LE.ZS.leProof where
    go :: LE.ZS.LEProof n' m' -> Vec m' a -> Vec n' a
    go LE.ZS.LEZero _              = VNil
    go (LE.ZS.LESucc p) (x ::: xs) = x ::: go p xs

-- |
--
-- >>> let xs = 'a' ::: 'b' ::: 'c' ::: 'd' ::: 'e' ::: VNil
-- >>> drop xs :: Vec N.Nat3 Char
-- 'c' ::: 'd' ::: 'e' ::: VNil
--
drop :: forall n m a. (LE.ZS.LE n m, N.SNatI m) => Vec m a -> Vec n a
drop = go (LE.RS.fromZeroSucc LE.ZS.leProof) where
    go :: LE.RS.LEProof n' m' -> Vec m' a -> Vec n' a
    go LE.RS.LERefl xs             = xs
    go (LE.RS.LEStep p) (_ ::: xs) = go p xs

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- | >>> map not $ True ::: False ::: VNil
-- False ::: True ::: VNil
--
map :: (a -> b) -> Vec n a -> Vec n b
map _ VNil       = VNil
map f (x ::: xs) = f x ::: fmap f xs

-- | >>> imap (,) $ 'a' ::: 'b' ::: 'c' ::: VNil
-- (0,'a') ::: (1,'b') ::: (2,'c') ::: VNil
--
imap :: (Fin n -> a -> b) -> Vec n a -> Vec n b
imap _ VNil       = VNil
imap f (x ::: xs) = f FZ x ::: imap (f . FS) xs

-- | Apply an action to every element of a 'Vec', yielding a 'Vec' of results.
traverse :: forall n f a b. Applicative f => (a -> f b) -> Vec n a -> f (Vec n b)
traverse f = go where
    go :: Vec m a -> f (Vec m b)
    go VNil       = pure VNil
    go (x ::: xs) = (:::) <$> f x <*> go xs

#ifdef MIN_VERSION_semigroupoids
-- | Apply an action to non-empty 'Vec', yielding a 'Vec' of results.
traverse1 :: forall n f a b. Apply f => (a -> f b) -> Vec ('S n) a -> f (Vec ('S n) b)
traverse1 f = go where
    go :: Vec ('S m) a -> f (Vec ('S m) b)
    go (x ::: VNil)         = (::: VNil) <$> f x
    go (x ::: xs@(_ ::: _)) = (:::) <$> f x <.> go xs
#endif

-- | Apply an action to every element of a 'Vec' and its index, yielding a 'Vec' of results.
itraverse :: Applicative f => (Fin n -> a -> f b) -> Vec n a -> f (Vec n b)
itraverse _ VNil       = pure VNil
itraverse f (x ::: xs) = (:::) <$> f FZ x <*> itraverse (f . FS) xs

-- | Apply an action to every element of a 'Vec' and its index, ignoring the results.
itraverse_ :: Applicative f => (Fin n -> a -> f b) -> Vec n a -> f ()
itraverse_ _ VNil       = pure ()
itraverse_ f (x ::: xs) = f FZ x *> itraverse_ (f . FS) xs

-------------------------------------------------------------------------------
-- Folding
-------------------------------------------------------------------------------

-- | See 'I.Foldable'.
foldMap :: Monoid m => (a -> m) -> Vec n a -> m
foldMap _ VNil       = mempty
foldMap f (x ::: xs) = mappend (f x) (foldMap f xs)

-- | See 'I.Foldable1'.
foldMap1 :: Semigroup s => (a -> s) -> Vec ('S n) a -> s
foldMap1 f (x ::: VNil)         = f x
foldMap1 f (x ::: xs@(_ ::: _)) = f x <> foldMap1 f xs

-- | See 'I.FoldableWithIndex'.
ifoldMap :: Monoid m => (Fin n -> a -> m) -> Vec n a -> m
ifoldMap _ VNil       = mempty
ifoldMap f (x ::: xs) = mappend (f FZ x) (ifoldMap (f . FS) xs)

-- | There is no type-class for this :(
ifoldMap1 :: Semigroup s => (Fin ('S n) -> a -> s) -> Vec ('S n) a -> s
ifoldMap1 f (x ::: VNil)         = f FZ x
ifoldMap1 f (x ::: xs@(_ ::: _)) = f FZ x <> ifoldMap1 (f . FS) xs

-- | Right fold.
foldr :: forall a b n. (a -> b -> b) -> b -> Vec n a -> b
foldr f z = go where
    go :: Vec m a -> b
    go VNil       = z
    go (x ::: xs) = f x (go xs)

-- | Right fold with an index.
ifoldr :: forall a b n. (Fin n -> a -> b -> b) -> b -> Vec n a -> b
ifoldr _ z VNil       = z
ifoldr f z (x ::: xs) = f FZ x (ifoldr (f . FS) z xs)

-- | Strict left fold.
foldl' :: forall a b n. (b -> a -> b) -> b -> Vec n a -> b
foldl' f z = go z where
    go :: b -> Vec m a -> b
    go !acc VNil       = acc
    go !acc (x ::: xs) = go (f acc x) xs

-- | Yield the length of a 'Vec'. /O(n)/
length :: Vec n a -> Int
length = go 0 where
    go :: Int -> Vec n a -> Int
    go !acc VNil       = acc
    go  acc (_ ::: xs) = go (1 + acc) xs

-- | Test whether a 'Vec' is empty. /O(1)/
null :: Vec n a -> Bool
null VNil      = True
null (_ ::: _) = False

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- | Non-strict 'sum'.
sum :: Num a => Vec n a -> a
sum VNil       = 0
sum (x ::: xs) = x + sum xs

-- | Non-strict 'product'.
product :: Num a => Vec n a -> a
product VNil       = 1
product (x ::: xs) = x * product xs

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'Vec's with a function.
zipWith ::  (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith _ VNil       VNil       = VNil
zipWith f (x ::: xs) (y ::: ys) = f x y ::: zipWith f xs ys

-- | Zip two 'Vec's. with a function that also takes the elements' indices.
izipWith :: (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
izipWith _ VNil       VNil       = VNil
izipWith f (x ::: xs) (y ::: ys) = f FZ x y ::: izipWith (f . FS) xs ys

-- | Repeat a value.
--
-- >>> repeat 'x' :: Vec N.Nat3 Char
-- 'x' ::: 'x' ::: 'x' ::: VNil
--
-- @since 0.2.1
repeat :: N.SNatI n => x -> Vec n x
repeat x = N.induction1 VNil (x :::)

-------------------------------------------------------------------------------
-- Monadic
-------------------------------------------------------------------------------

-- | Monadic bind.
bind :: Vec n a -> (a -> Vec n b) -> Vec n b
bind VNil       _ = VNil
bind (x ::: xs) f = head (f x) ::: bind xs (tail . f)

-- | Monadic join.
--
-- >>> join $ ('a' ::: 'b' ::: VNil) ::: ('c' ::: 'd' ::: VNil) ::: VNil
-- 'a' ::: 'd' ::: VNil
join :: Vec n (Vec n a) -> Vec n a
join VNil       = VNil
join (x ::: xs) = head x ::: join (map tail xs)

-------------------------------------------------------------------------------
-- universe
-------------------------------------------------------------------------------

-- | Get all @'Fin' n@ in a @'Vec' n@.
--
-- >>> universe :: Vec N.Nat3 (Fin N.Nat3)
-- 0 ::: 1 ::: 2 ::: VNil
universe :: N.SNatI n => Vec n (Fin n)
universe = getUniverse (N.induction first step) where
    first :: Universe 'Z
    first = Universe VNil

    step :: Universe m -> Universe ('S m)
    step (Universe go) = Universe (FZ ::: map FS go)

newtype Universe n = Universe { getUniverse :: Vec n (Fin n) }

-------------------------------------------------------------------------------
-- VecEach
-------------------------------------------------------------------------------

-- | Write functions on 'Vec'. Use them with tuples.
--
-- 'VecEach' can be used to avoid "this function won't change the length of the
-- list" in DSLs.
--
-- __bad:__ Instead of
--
-- @
-- [x, y] <- badDslMagic ["foo", "bar"]  -- list!
-- @
--
-- __good:__ we can write
--
-- @
-- (x, y) <- betterDslMagic ("foo", "bar") -- homogenic tuple!
-- @
--
-- where @betterDslMagic@ can be defined using 'traverseWithVec'.
--
-- Moreally @lens@ 'Each' should be a superclass, but
-- there's no strict need for it.
--
class VecEach s t a b | s -> a, t -> b, s b -> t, t a -> s where
    mapWithVec :: (forall n. N.SNatI n => Vec n a -> Vec n b) -> s -> t
    traverseWithVec :: Applicative f => (forall n. N.SNatI n => Vec n a -> f (Vec n b)) -> s -> f t

instance (a ~ a', b ~ b') => VecEach (a, a') (b, b') a b where
    mapWithVec f ~(x, y) = case f (x ::: y ::: VNil) of
        x' ::: y' ::: VNil -> (x', y')

    traverseWithVec f ~(x, y) = f (x ::: y ::: VNil) <&> \res -> case res of
        x' ::: y' ::: VNil -> (x', y')

instance (a ~ a2, a ~ a3, b ~ b2, b ~ b3) => VecEach (a, a2, a3) (b, b2, b3) a b where
    mapWithVec f ~(x, y, z) = case f (x ::: y ::: z ::: VNil) of
        x' ::: y' ::: z' ::: VNil -> (x', y', z')

    traverseWithVec f ~(x, y, z) = f (x ::: y ::: z ::: VNil) <&> \res -> case res of
        x' ::: y' ::: z' ::: VNil -> (x', y', z')

instance (a ~ a2, a ~ a3, a ~ a4, b ~ b2, b ~ b3, b ~ b4) => VecEach (a, a2, a3, a4) (b, b2, b3, b4) a b where
    mapWithVec f ~(x, y, z, u) = case f (x ::: y ::: z ::: u ::: VNil) of
        x' ::: y' ::: z' ::: u' ::: VNil -> (x', y', z', u')

    traverseWithVec f ~(x, y, z, u) = f (x ::: y ::: z ::: u ::: VNil) <&> \res -> case res of
        x' ::: y' ::: z' ::: u' ::: VNil -> (x', y', z', u')

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance N.SNatI n => QC.Arbitrary1 (Vec n) where
    liftArbitrary = liftArbitrary
    liftShrink    = liftShrink

liftArbitrary :: forall n a. N.SNatI n => QC.Gen a -> QC.Gen (Vec n a)
liftArbitrary arb = getArb $ N.induction1 (Arb (return VNil)) step where
    step :: Arb m a -> Arb ('S m) a
    step (Arb rec) = Arb $ (:::) <$> arb <*> rec

newtype Arb n a = Arb { getArb :: QC.Gen (Vec n a) }

liftShrink :: forall n a. N.SNatI n => (a -> [a]) -> Vec n a -> [Vec n a]
liftShrink shr = getShr $ N.induction1 (Shr $ \VNil -> []) step where
    step :: Shr m a -> Shr ('S m) a
    step (Shr rec) = Shr $ \(x ::: xs) ->
        uncurry (:::) <$> QC.liftShrink2 shr rec (x, xs)

newtype Shr n a = Shr { getShr :: Vec n a -> [Vec n a] }

instance (N.SNatI n, QC.Arbitrary a) => QC.Arbitrary (Vec n a) where
    arbitrary = QC.arbitrary1
    shrink    = QC.shrink1

instance (N.SNatI n, QC.CoArbitrary a) => QC.CoArbitrary (Vec n a) where
    coarbitrary v = case N.snat :: N.SNat n of
        N.SZ -> QC.variant (0 :: Int)
        N.SS -> QC.variant (1 :: Int) . (case v of (x ::: xs) -> QC.coarbitrary (x, xs))

instance (N.SNatI n, QC.Function a) => QC.Function (Vec n a) where
    function = case N.snat :: N.SNat n of
        N.SZ -> QC.functionMap (\VNil -> ()) (\() -> VNil)
        N.SS -> QC.functionMap (\(x ::: xs) -> (x, xs)) (\(x,xs) -> x ::: xs)
