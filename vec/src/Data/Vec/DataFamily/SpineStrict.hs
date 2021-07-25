{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Spine-strict length-indexed list defined as data-family: 'Vec'.
--
-- Data family variant allows  lazy pattern matching.
-- On the other hand, the 'Vec' value doesn't "know" its length (i.e. there isn't 'Data.Vec.Lazy.withDict').
--
-- == Agda
--
-- If you happen to familiar with Agda, then the difference
-- between GADT and data-family version is maybe clearer:
--
-- @
-- module Vec where
--
-- open import Data.Nat
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
--
-- -- \"GADT"
-- data Vec (A : Set) : ℕ → Set where
--   []  : Vec A 0
--   _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
--
-- infixr 50 _∷_
--
-- exVec : Vec ℕ 2
-- exVec = 13 ∷ 37 ∷ []
--
-- -- "data family"
-- data Unit : Set where
--   [] : Unit
--
-- data _×_ (A B : Set) : Set where
--   _∷_ : A → B → A × B
--
-- infixr 50 _×_
--
-- VecF : Set → ℕ → Set
-- VecF A zero    = Unit
-- VecF A (suc n) = A × VecF A n
--
-- exVecF : VecF ℕ 2
-- exVecF = 13 ∷ 37 ∷ []
--
-- reduction : VecF ℕ 2 ≡ ℕ × ℕ × Unit
-- reduction = refl
-- @
--
module Data.Vec.DataFamily.SpineStrict (
    Vec (..),
    -- * Construction
    empty,
    singleton,
    -- * Conversions
    toPull,
    fromPull,
    toList,
    toNonEmpty,
    fromList,
    fromListPrefix,
    reifyList,
    -- * Indexing
    (!),
    tabulate,
    cons,
    snoc,
    head,
    last,
    tail,
    init,
    -- * Reverse
    reverse,
    -- * Concatenation and splitting
    (++),
    split,
    concatMap,
    concat,
    chunks,
    -- * Folds
    foldMap,
    foldMap1,
    ifoldMap,
    ifoldMap1,
    foldr,
    ifoldr,
    -- * Scans
    scanr,
    scanl,
    scanr1,
    scanl1,
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
    -- * Extras
    ensureSpine,
    ) where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Maybe (..), Monad (..), Num (..),
       Ord (..), Ordering (EQ), Show (..), ShowS, const, flip, id, seq,
       showParen, showString, uncurry, ($), (&&), (.))

import Control.Applicative (Applicative (..), liftA2, (<$>))
import Control.DeepSeq     (NFData (..))
import Data.Fin            (Fin (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Hashable       (Hashable (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Semigroup      (Semigroup (..))

--- Instances
import qualified Data.Foldable    as I (Foldable (..))
import qualified Data.Traversable as I (Traversable (..))
import qualified Test.QuickCheck  as QC

import qualified Data.Foldable.WithIndex    as WI (FoldableWithIndex (..))
import qualified Data.Functor.WithIndex     as WI (FunctorWithIndex (..))
import qualified Data.Traversable.WithIndex as WI (TraversableWithIndex (..))

import Data.Functor.Classes (Eq1 (..), Ord1 (..), Show1 (..))

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

-- $setup
-- >>> :set -XScopedTypeVariables -XDataKinds
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Control.Applicative ((<$>))
-- >>> import Prelude (Char, not, uncurry, error, Eq (..), Ord (..), Bool (..), Maybe (..), ($), id, (.), Int)
-- >>> import qualified Data.Type.Nat as N
-- >>> import Data.Fin (Fin (..))
-- >>> import Data.Nat (Nat (..))

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

infixr 5 :::

-- | Vector, i.e. length-indexed list.
data family   Vec (n :: Nat) a
data instance Vec 'Z     a = VNil
data instance Vec ('S n) a = a ::: !(Vec n a)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

-- |
--
-- >>> 'a' ::: 'b' ::: VNil == 'a' ::: 'c' ::: VNil
-- False
instance (Eq a, N.SNatI n) => Eq (Vec n a) where
    (==) = getEqual (N.induction start step) where
        start :: Equal a a 'Z
        start = Equal $ \_ _ -> True

        step :: Equal a a m -> Equal a a ('S m)
        step (Equal go) = Equal $ \(x ::: xs) (y ::: ys) ->
            x == y && go xs ys

newtype Equal a b n = Equal { getEqual :: Vec n a -> Vec n b -> Bool }

-- |
--
-- >>> compare ('a' ::: 'b' ::: VNil) ('a' ::: 'c' ::: VNil)
-- LT
instance (Ord a, N.SNatI n) => Ord (Vec n a) where
    compare = getCompare (N.induction start step) where
        start :: Compare a a 'Z
        start = Compare $ \_ _ -> EQ

        step :: Compare a a m -> Compare a a ('S m)
        step (Compare go) = Compare $ \(x ::: xs) (y ::: ys) ->
            compare x y <> go xs ys

newtype Compare a b n = Compare { getCompare :: Vec n a -> Vec n b -> Ordering }

instance (Show a, N.SNatI n) => Show (Vec n a) where
    showsPrec = getShowsPrec (N.induction1 start step) where
        start :: ShowsPrec 'Z a
        start = ShowsPrec $ \_ _ -> showString "VNil"

        step :: ShowsPrec m a -> ShowsPrec ('S m) a
        step (ShowsPrec go) = ShowsPrec $ \d (x ::: xs) -> showParen (d > 5)
            $ showsPrec 6 x
            . showString " ::: "
            . go 5 xs

newtype ShowsPrec n a = ShowsPrec { getShowsPrec :: Int -> Vec n a -> ShowS }

instance N.SNatI n => Functor (Vec n) where
    fmap = map

instance N.SNatI n => I.Foldable (Vec n) where
    foldMap = foldMap

    foldr  = foldr
    -- foldl' = foldl'

#if MIN_VERSION_base(4,8,0)
    null    = null
    length  = length
    sum     = sum
    product = product
#endif

#ifdef MIN_VERSION_semigroupoids
instance (N.SNatI m, n ~ 'S m) => I.Foldable1 (Vec n) where
    foldMap1 = foldMap1

instance (N.SNatI m, n ~ 'S m) => I.Traversable1 (Vec n) where
    traverse1 = traverse1
#endif

instance N.SNatI n => I.Traversable (Vec n) where
    traverse = traverse

-- | @since 0.4
instance N.SNatI n => WI.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

-- | @since 0.4
instance N.SNatI n => WI.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

-- | @since 0.4
instance N.SNatI n => WI.TraversableWithIndex (Fin n) (Vec n) where
    itraverse = itraverse

instance (NFData a, N.SNatI n) => NFData (Vec n a) where
    rnf = getRnf (N.induction1 z s) where
        z           = Rnf $ \VNil -> ()
        s (Rnf rec) = Rnf $ \(x ::: xs) -> rnf x `seq` rec xs

newtype Rnf n a = Rnf { getRnf :: Vec n a -> () }

instance (Hashable a, N.SNatI n) => Hashable (Vec n a) where
    hashWithSalt = getHashWithSalt (N.induction1 z s) where
        z = HashWithSalt $ \salt VNil -> salt `hashWithSalt` (0 :: Int)
        s (HashWithSalt rec) = HashWithSalt $ \salt (x ::: xs) -> rec (salt
            `hashWithSalt` x) xs

newtype HashWithSalt n a = HashWithSalt { getHashWithSalt :: Int -> Vec n a -> Int }

instance N.SNatI n => Applicative (Vec n) where
    pure x = N.induction1 VNil (x :::)
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

instance (Semigroup a, N.SNatI n) => Semigroup (Vec n a) where
    (<>) = zipWith (<>)

instance (Monoid a, N.SNatI n) => Monoid (Vec n a) where
    mempty = pure mempty
    mappend = zipWith mappend

#ifdef MIN_VERSION_semigroupoids
instance N.SNatI n => Apply (Vec n) where
    (<.>) = zipWith ($)
    _ .> x = x
    x <. _ = x
    liftF2 = zipWith

instance N.SNatI n => I.Bind (Vec n) where
    (>>-) = bind
    join  = join
#endif

-------------------------------------------------------------------------------
-- Data.Functor.Classes
-------------------------------------------------------------------------------

#ifndef MIN_VERSION_transformers_compat
#define MIN_VERSION_transformers_compat(x,y,z) 0
#endif


#if MIN_VERSION_base(4,9,0)
#define LIFTED_FUNCTOR_CLASSES 1
#else
#if MIN_VERSION_transformers(0,5,0)
#define LIFTED_FUNCTOR_CLASSES 1
#else
#if MIN_VERSION_transformers_compat(0,5,0) && !MIN_VERSION_transformers(0,4,0)
#define LIFTED_FUNCTOR_CLASSES 1
#endif
#endif
#endif

#if LIFTED_FUNCTOR_CLASSES

-- | @since 0.4
instance N.SNatI n => Eq1 (Vec n) where
    liftEq :: forall a b. (a -> b -> Bool) -> Vec n a -> Vec n b -> Bool
    liftEq eq = getEqual (N.induction start step) where
        start :: Equal a b 'Z
        start = Equal $ \_ _ -> True

        step :: Equal a b m -> Equal a b ('S m)
        step (Equal go) = Equal $ \(x ::: xs) (y ::: ys) ->
            eq x y && go xs ys

-- | @since 0.4
instance N.SNatI n => Ord1 (Vec n) where
    liftCompare :: forall a b. (a -> b -> Ordering) -> Vec n a -> Vec n b -> Ordering
    liftCompare cmp = getCompare (N.induction start step) where
        start :: Compare a b 'Z
        start = Compare $ \_ _ -> EQ

        step :: Compare a b m -> Compare a b ('S m)
        step (Compare go) = Compare $ \(x ::: xs) (y ::: ys) ->
            cmp x y <> go xs ys

-- | @since 0.4
instance N.SNatI n => Show1 (Vec n) where
    liftShowsPrec :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Vec n a -> ShowS
    liftShowsPrec sp _ = getShowsPrec (N.induction1 start step) where
        start :: ShowsPrec 'Z a
        start = ShowsPrec $ \_ _ -> showString "VNil"

        step :: ShowsPrec m a -> ShowsPrec ('S m) a
        step (ShowsPrec go) = ShowsPrec $ \d (x ::: xs) -> showParen (d > 5)
            $ sp 6 x
            . showString " ::: "
            . go 5 xs
#else
-- | @since 0.4
instance N.SNatI n => Eq1 (Vec n) where eq1 = (==)

-- | @since 0.4
instance N.SNatI n => Ord1 (Vec n) where compare1 = compare

-- | @since 0.4
instance N.SNatI n => Show1 (Vec n) where showsPrec1 = showsPrec
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

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert to pull 'P.Vec'.
toPull :: forall n a. N.SNatI n => Vec n a -> P.Vec n a
toPull = getToPull (N.induction1 start step) where
    start :: ToPull 'Z a
    start = ToPull $ \_ -> P.Vec F.absurd

    step :: ToPull m a -> ToPull ('S m) a
    step (ToPull f) = ToPull $ \(x ::: xs) -> P.Vec $ \i -> case i of
        FZ    -> x
        FS i' -> P.unVec (f xs) i'

newtype ToPull n a = ToPull { getToPull :: Vec n a -> P.Vec n a }

-- | Convert from pull 'P.Vec'.
fromPull :: forall n a. N.SNatI n => P.Vec n a -> Vec n a
fromPull = getFromPull (N.induction1 start step) where
    start :: FromPull 'Z a
    start = FromPull $ const VNil

    step :: FromPull m a -> FromPull ('S m) a
    step (FromPull f) = FromPull $ \(P.Vec v) -> v FZ ::: f (P.Vec (v . FS))

newtype FromPull n a = FromPull { getFromPull :: P.Vec n a -> Vec n a }

-- | Convert 'Vec' to list.
--
-- >>> toList $ 'f' ::: 'o' ::: 'o' ::: VNil
-- "foo"
toList :: forall n a. N.SNatI n => Vec n a -> [a]
toList = getToList (N.induction1 start step) where
    start :: ToList 'Z a
    start = ToList (const [])

    step :: ToList m a -> ToList ('S m) a
    step (ToList f) = ToList $ \(x ::: xs) -> x : f xs

newtype ToList n a = ToList { getToList :: Vec n a -> [a] }

-- |
--
-- >>> toNonEmpty $ 1 ::: 2 ::: 3 ::: VNil
-- 1 :| [2,3]
--
-- @since 0.4
toNonEmpty :: forall n a. N.SNatI n => Vec ('S n) a -> NonEmpty a
toNonEmpty (x ::: xs) = x :| toList xs

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

flipIndex :: N.SNatI n => Fin n -> Vec n a -> a
flipIndex = getIndex (N.induction1 start step) where
    start :: Index 'Z a
    start = Index F.absurd

    step :: Index m a-> Index ('N.S m) a
    step (Index go) = Index $ \n (x ::: xs) -> case n of
        FZ   -> x
        FS m -> go m xs

newtype Index n a = Index { getIndex :: Fin n -> Vec n a -> a }

-- | Indexing.
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) ! FS FZ
-- 'b'
--
(!) :: N.SNatI n => Vec n a -> Fin n -> a
(!) = flip flipIndex

-- | Tabulating, inverse of '!'.
--
-- >>> tabulate id :: Vec N.Nat3 (Fin N.Nat3)
-- 0 ::: 1 ::: 2 ::: VNil
tabulate :: N.SNatI n => (Fin n -> a) -> Vec n a
tabulate = fromPull . P.tabulate

-- | Cons an element in front of a 'Vec'.
cons :: a -> Vec n a -> Vec ('S n) a
cons = (:::)

-- | Add a single element at the end of a 'Vec'.
snoc :: forall n a. N.SNatI n => Vec n a -> a -> Vec ('S n) a
snoc xs x = getSnoc (N.induction1 start step) xs where
    start :: Snoc 'Z a
    start = Snoc $ \ys -> x ::: ys

    step :: Snoc m a -> Snoc ('S m) a
    step (Snoc rec) = Snoc $ \(y ::: ys) -> y ::: rec ys

newtype Snoc n a = Snoc { getSnoc :: Vec n a -> Vec ('S n) a }

-- | The first element of a 'Vec'.
head :: Vec ('S n) a -> a
head (x ::: _) = x

-- | The elements after the 'head' of a 'Vec'.
tail :: Vec ('S n) a -> Vec n a
tail (_ ::: xs) = xs

-- | The last element of a 'Vec'.
--
-- @since 0.4
last :: forall n a. N.SNatI n => Vec ('S n) a -> a
last xs = getLast (N.induction1 start step) xs where
    start :: Last 'Z a
    start = Last $ \(x:::VNil) -> x

    step :: Last m a -> Last ('S m) a
    step (Last rec) = Last $ \(_ ::: ys) -> rec ys


newtype Last n a = Last { getLast :: Vec ('S n) a -> a }

-- | The elements before the 'last' of a 'Vec'.
--
-- @since 0.4
init :: forall n a. N.SNatI n => Vec ('S n) a -> Vec n a
init xs = getInit (N.induction1 start step) xs where
    start :: Init 'Z a
    start = Init (const VNil)

    step :: Init m a -> Init ('S m) a
    step (Init rec) = Init $ \(y ::: ys) -> y ::: rec ys

newtype Init n a = Init { getInit :: Vec ('S n) a -> Vec n a}

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
reverse :: forall n a. N.SNatI n => Vec n a -> Vec n a
reverse = getReverse (N.induction1 start step) where
    start :: Reverse 'Z a
    start = Reverse $ \_ -> VNil

    step :: N.SNatI m => Reverse m a -> Reverse ('S m) a
    step (Reverse rec) = Reverse $ \(x ::: xs) -> snoc (rec xs) x

newtype Reverse n a = Reverse { getReverse :: Vec n a -> Vec n a }

-------------------------------------------------------------------------------
-- Concatenation
-------------------------------------------------------------------------------

infixr 5 ++

-- | Append two 'Vec'.
--
-- >>> ('a' ::: 'b' ::: VNil) ++ ('c' ::: 'd' ::: VNil)
-- 'a' ::: 'b' ::: 'c' ::: 'd' ::: VNil
--
(++) :: forall n m a. N.SNatI n => Vec n a -> Vec m a -> Vec (N.Plus n m) a
as ++ ys = getAppend (N.induction1 start step) as where
    start :: Append m 'Z a
    start = Append $ \_ -> ys

    step :: Append m p a -> Append m ('S p) a
    step (Append f) = Append $ \(x ::: xs) -> x ::: f xs

newtype Append m n a = Append { getAppend :: Vec n a -> Vec (N.Plus n m) a }

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
concatMap :: forall a b n m. (N.SNatI m, N.SNatI n) => (a -> Vec m b) -> Vec n a -> Vec (N.Mult n m) b
concatMap f = getConcatMap $ N.induction1 start step where
    start :: ConcatMap m a 'Z b
    start = ConcatMap $ \_ -> VNil

    step :: ConcatMap m a p b -> ConcatMap m a ('S p) b
    step (ConcatMap g) = ConcatMap $ \(x ::: xs) -> f x ++ g xs

newtype ConcatMap m a n b = ConcatMap { getConcatMap :: Vec n a -> Vec (N.Mult n m) b }

-- | @'concatMap' 'id'@
concat :: (N.SNatI m, N.SNatI n) => Vec n (Vec m a) -> Vec (N.Mult n m) a
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
-- Mapping
-------------------------------------------------------------------------------

-- | >>> map not $ True ::: False ::: VNil
-- False ::: True ::: VNil
--
map :: forall a b n. N.SNatI n => (a -> b) -> Vec n a -> Vec n b
map f = getMap $ N.induction1 start step where
    start :: Map a 'Z b
    start = Map $ \_ -> VNil

    step :: Map a m b -> Map a ('S m) b
    step (Map go) = Map $ \(x ::: xs) -> f x ::: go xs

newtype Map a n b = Map { getMap :: Vec n a -> Vec n b }

-- | >>> imap (,) $ 'a' ::: 'b' ::: 'c' ::: VNil
-- (0,'a') ::: (1,'b') ::: (2,'c') ::: VNil
--
imap :: N.SNatI n => (Fin n -> a -> b) -> Vec n a -> Vec n b
imap = getIMap $ N.induction1 start step where
    start :: IMap a 'Z b
    start = IMap $ \_ _ -> VNil

    step :: IMap a m b -> IMap a ('S m) b
    step (IMap go) = IMap $ \f (x ::: xs) -> f FZ x ::: go (f . FS) xs

newtype IMap a n b = IMap { getIMap :: (Fin n -> a -> b) -> Vec n a -> Vec n b }

-- | Apply an action to every element of a 'Vec', yielding a 'Vec' of results.
traverse :: forall n f a b. (Applicative f, N.SNatI n) => (a -> f b) -> Vec n a -> f (Vec n b)
traverse f =  getTraverse $ N.induction1 start step where
    start :: Traverse f a 'Z b
    start = Traverse $ \_ -> pure VNil

    step :: Traverse f a m b -> Traverse f a ('S m) b
    step (Traverse go) = Traverse $ \(x ::: xs) -> liftA2 (:::) (f x) (go xs)
{-# INLINE traverse #-}

newtype Traverse f a n b = Traverse { getTraverse :: Vec n a -> f (Vec n b) }

#ifdef MIN_VERSION_semigroupoids
-- | Apply an action to non-empty 'Vec', yielding a 'Vec' of results.
traverse1 :: forall n f a b. (Apply f, N.SNatI n) => (a -> f b) -> Vec ('S n) a -> f (Vec ('S n) b)
traverse1 f = getTraverse1 $ N.induction1 start step where
    start :: Traverse1 f a 'Z b
    start = Traverse1 $ \(x ::: _) -> (::: VNil) <$> f x

    step :: Traverse1 f a m b -> Traverse1 f a ('S m) b
    step (Traverse1 go) = Traverse1 $ \(x ::: xs) -> liftF2 (:::) (f x) (go xs)

newtype Traverse1 f a n b = Traverse1 { getTraverse1 :: Vec ('S n) a -> f (Vec ('S n) b) }
#endif

-- | Apply an action to every element of a 'Vec' and its index, yielding a 'Vec' of results.
itraverse :: forall n f a b. (Applicative f, N.SNatI n) => (Fin n -> a -> f b) -> Vec n a -> f (Vec n b)
itraverse = getITraverse $ N.induction1 start step where
    start :: ITraverse f a 'Z b
    start = ITraverse $ \_ _ -> pure VNil

    step :: ITraverse f a m b -> ITraverse f a ('S m) b
    step (ITraverse go) = ITraverse $ \f (x ::: xs) -> liftA2 (:::) (f FZ x) (go (f . FS) xs)
{-# INLINE itraverse #-}

newtype ITraverse f a n b = ITraverse { getITraverse :: (Fin n -> a -> f b) -> Vec n a -> f (Vec n b) }

-- | Apply an action to every element of a 'Vec' and its index, ignoring the results.
itraverse_ :: forall n f a b. (Applicative f, N.SNatI n) => (Fin n -> a -> f b) -> Vec n a -> f ()
itraverse_ = getITraverse_ $ N.induction1 start step where
    start :: ITraverse_ f a 'Z b
    start = ITraverse_ $ \_ _ -> pure ()

    step :: ITraverse_ f a m b -> ITraverse_ f a ('S m) b
    step (ITraverse_ go) = ITraverse_ $ \f (x ::: xs) -> f FZ x *> go (f . FS) xs

newtype ITraverse_ f a n b = ITraverse_ { getITraverse_ :: (Fin n -> a -> f b) -> Vec n a -> f () }

-------------------------------------------------------------------------------
-- Folding
-------------------------------------------------------------------------------

-- | See 'I.Foldable'.
foldMap :: (Monoid m, N.SNatI n) => (a -> m) -> Vec n a -> m
foldMap f = getFold $ N.induction1 (Fold (const mempty)) $ \(Fold go) ->
    Fold $ \(x ::: xs) -> f x `mappend` go xs

newtype Fold  a n b = Fold  { getFold  :: Vec n a -> b }

-- | See 'I.Foldable1'.
foldMap1 :: forall s a n. (Semigroup s, N.SNatI n) => (a -> s) -> Vec ('S n) a -> s
foldMap1 f = getFold1 $ N.induction1 start step where
    start :: Fold1 a 'Z s
    start = Fold1 $ \(x ::: _) -> f x

    step :: Fold1 a m s -> Fold1 a ('S m) s
    step (Fold1 g) = Fold1 $ \(x ::: xs) -> f x <> g xs

newtype Fold1 a n b = Fold1 { getFold1 :: Vec ('S n) a -> b }

-- | See 'I.FoldableWithIndex'.
ifoldMap :: forall a n m. (Monoid m, N.SNatI n) => (Fin n -> a -> m) -> Vec n a -> m
ifoldMap = getIFoldMap $ N.induction1 start step where
    start :: IFoldMap a 'Z m
    start = IFoldMap $ \_ _ -> mempty

    step :: IFoldMap a p m -> IFoldMap a ('S p) m
    step (IFoldMap go) = IFoldMap $ \f (x ::: xs) -> f FZ x `mappend` go (f . FS) xs

newtype IFoldMap a n m = IFoldMap { getIFoldMap :: (Fin n -> a -> m) -> Vec n a -> m }

-- | There is no type-class for this :(
ifoldMap1 :: forall a n s. (Semigroup s, N.SNatI n) => (Fin ('S n) -> a -> s) -> Vec ('S n) a -> s
ifoldMap1 = getIFoldMap1 $ N.induction1 start step where
    start :: IFoldMap1 a 'Z s
    start = IFoldMap1 $ \f (x ::: _) -> f FZ x

    step :: IFoldMap1 a p s -> IFoldMap1 a ('S p) s
    step (IFoldMap1 go) = IFoldMap1 $ \f (x ::: xs) -> f FZ x <> go (f . FS) xs

newtype IFoldMap1 a n m = IFoldMap1 { getIFoldMap1 :: (Fin ('S n) -> a -> m) -> Vec ('S n) a -> m }

-- | Right fold.
foldr :: forall a b n. N.SNatI n => (a -> b -> b) -> b -> Vec n a -> b
foldr f z = getFold $ N.induction1 start step where
    start :: Fold a 'Z b
    start = Fold $ \_ -> z

    step :: Fold a m b -> Fold a ('S m) b
    step (Fold go) = Fold $ \(x ::: xs) -> f x (go xs)

-- | Right fold with an index.
ifoldr :: forall a b n. N.SNatI n => (Fin n -> a -> b -> b) -> b -> Vec n a -> b
ifoldr = getIFoldr $ N.induction1 start step where
    start :: IFoldr a 'Z b
    start = IFoldr $ \_ z _ -> z

    step :: IFoldr a m b -> IFoldr a ('S m) b
    step (IFoldr go) = IFoldr $ \f z (x ::: xs) -> f FZ x (go (f . FS) z xs)

newtype IFoldr a n b = IFoldr { getIFoldr :: (Fin n -> a -> b -> b) -> b -> Vec n a -> b }

scanr :: forall a b n. N.SNatI n => (a -> b -> b) -> b -> Vec n a -> Vec ('S n) b
scanr f z = getScan $ N.induction1 start step where
    start :: Scan a 'Z b
    start = Scan $ \_ -> singleton z

    step :: Scan a m b -> Scan a ('S m) b
    step (Scan go) = Scan $ \(x ::: xs) -> let ys@(y ::: _) = go xs in f x y ::: ys

newtype Scan a n b = Scan { getScan :: Vec n a -> Vec ('S n) b }

scanl :: forall a b n. N.SNatI n => (b -> a -> b) -> b -> Vec n a -> Vec ('S n) b
scanl f z = reverse . scanr (flip f) z . reverse

scanr1 :: forall a n. N.SNatI n => (a -> a -> a) -> Vec n a -> Vec n a
scanr1 f = getScan1 $ N.induction1 start step where
    start :: Scan1 'Z a
    start = Scan1 $ \_ -> VNil

    step :: forall m. N.SNatI m => Scan1 m a -> Scan1 ('S m) a
    step (Scan1 go) = Scan1 $ \(x ::: xs) -> case N.snat :: N.SNat m of
        N.SZ -> x ::: VNil
        N.SS -> let ys@(y ::: _) = go xs in f x y ::: ys

newtype Scan1 n a = Scan1 { getScan1 :: Vec n a -> Vec n a }

scanl1 :: forall a n. N.SNatI n => (a -> a -> a) -> Vec n a -> Vec n a
scanl1 f xs = case N.snat :: N.SNat n of
    N.SZ -> VNil
    N.SS -> let (y ::: ys) = xs in scanl f y ys

-- | Yield the length of a 'Vec'. /O(n)/
length :: forall n a. N.SNatI n => Vec n a -> Int
length _ = getLength l where
    l :: Length n
    l = N.induction (Length 0) $ \(Length n) -> Length (1 + n)

newtype Length (n :: Nat) = Length { getLength :: Int }

-- | Test whether a 'Vec' is empty. /O(1)/
null :: forall n a. N.SNatI n => Vec n a -> Bool
null _ = case N.snat :: N.SNat n of
    N.SZ -> True
    N.SS -> False

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- | Non-strict 'sum'.
sum :: (Num a, N.SNatI n) => Vec n a -> a
sum = getFold $ N.induction1 start step where
    start :: Num a => Fold a 'Z a
    start = Fold $ \_ -> 0

    step :: Num a => Fold a m a -> Fold a ('S m) a
    step (Fold f) = Fold $ \(x ::: xs) -> x + f xs

-- | Non-strict 'product'.
product :: (Num a, N.SNatI n) => Vec n a -> a
product = getFold $ N.induction1 start step where
    start :: Num a => Fold a 'Z a
    start = Fold $ \_ -> 1

    step :: Num a => Fold a m a -> Fold a ('S m) a
    step (Fold f) = Fold $ \(x ::: xs) -> x * f xs


-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'Vec's with a function.
zipWith :: forall a b c n. N.SNatI n => (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f = getZipWith $ N.induction start step where
    start :: ZipWith a b c 'Z
    start = ZipWith $ \_ _ -> VNil

    step :: ZipWith a b c m -> ZipWith a b c ('S m)
    step (ZipWith go) = ZipWith $ \(x ::: xs) (y ::: ys) -> f x y ::: go xs ys

newtype ZipWith a b c n = ZipWith { getZipWith :: Vec n a -> Vec n b -> Vec n c }

-- | Zip two 'Vec's. with a function that also takes the elements' indices.
izipWith :: N.SNatI n => (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
izipWith = getIZipWith $ N.induction start step where
    start :: IZipWith a b c 'Z
    start = IZipWith $ \_ _ _ -> VNil

    step :: IZipWith a b c m -> IZipWith a b c ('S m)
    step (IZipWith go) = IZipWith $ \f (x ::: xs) (y ::: ys) -> f FZ x y ::: go (f . FS) xs ys

newtype IZipWith a b c n = IZipWith { getIZipWith :: (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c }

-- | Repeat value
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
bind :: N.SNatI n => Vec n a -> (a -> Vec n b) -> Vec n b
bind = getBind $ N.induction1 start step where
    start :: Bind a 'Z b
    start = Bind $ \_ _ -> VNil

    step :: Bind a m b -> Bind a ('S m) b
    step (Bind go) = Bind $ \(x ::: xs) f -> head (f x) ::: go xs (tail . f)

newtype Bind a n b = Bind { getBind :: Vec n a -> (a -> Vec n b) -> Vec n b }

-- | Monadic join.
--
-- >>> join $ ('a' ::: 'b' ::: VNil) ::: ('c' ::: 'd' ::: VNil) ::: VNil
-- 'a' ::: 'd' ::: VNil
join :: N.SNatI n => Vec n (Vec n a) -> Vec n a
join = getJoin $ N.induction1 start step where
    start :: Join 'Z a
    start = Join $ \_ -> VNil

    step :: N.SNatI m => Join m a -> Join ('S m) a
    step (Join go) = Join $ \(x ::: xs) -> head x ::: go (map tail xs)

newtype Join n a = Join { getJoin :: Vec n (Vec n a) -> Vec n a }

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

    step :: N.SNatI m => Universe m -> Universe ('S m)
    step (Universe go) = Universe (FZ ::: map FS go)

newtype Universe n = Universe { getUniverse :: Vec n (Fin n) }

-------------------------------------------------------------------------------
-- EnsureSpine
-------------------------------------------------------------------------------

-- | Ensure spine.
--
-- If we have an undefined 'Vec',
--
-- >>> let v = error "err" :: Vec N.Nat3 Char
--
-- And insert data into it later:
--
-- >>> let setHead :: a -> Vec ('S n) a -> Vec ('S n) a; setHead x (_ ::: xs) = x ::: xs
--
-- Then without a spine, it will fail:
--
-- >>> head $ setHead 'x' v
-- *** Exception: err
-- ...
--
-- But with the spine, it won't:
--
-- >>> head $ setHead 'x' $ ensureSpine v
-- 'x'
--
ensureSpine :: N.SNatI n => Vec n a -> Vec n a
ensureSpine = getEnsureSpine (N.induction1 first step) where
    first :: EnsureSpine 'Z a
    first = EnsureSpine $ \_ -> VNil

    step :: EnsureSpine m a -> EnsureSpine ('S m) a
    step (EnsureSpine go) = EnsureSpine $ \ ~(x ::: xs) -> x ::: go xs

newtype EnsureSpine n a = EnsureSpine { getEnsureSpine :: Vec n a -> Vec n a }

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
