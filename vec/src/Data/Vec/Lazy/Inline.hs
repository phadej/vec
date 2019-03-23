{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | A variant of "Data.Vec.Lazy" with functions written using 'N.InlineInduction'.
-- The hypothesis is that these (goursive) functions could be fully unrolled,
-- if the 'Vec' size @n@ is known at compile time.
--
-- The module has the same API as "Data.Vec.Lazy" (sans 'L.withDict' and 'foldl'').
-- /Note:/ instance methods aren't changed, the 'Vec' type is the same.
module Data.Vec.Lazy.Inline (
    Vec (..),
    -- * Construction
    empty,
    singleton,
    -- * Conversions
    toPull,
    fromPull,
    _Pull,
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
    cons,
    head,
    tail,
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
    -- * Special folds
    length,
    null,
    sum,
    product,
    -- * Mapping
    map,
    imap,
    traverse,
    traverse1,
    itraverse,
    itraverse_,
    -- * Zipping
    zipWith,
    izipWith,
    -- * Monadic
    bind,
    join,
    -- * Universe
    universe,
    -- * VecEach
    VecEach (..)
    )  where

import Prelude ()
import Prelude.Compat
       (Applicative (..), Int, Maybe (..), Monoid (..), Num (..), const, flip,
       id, ($), (.), (<$>))

import Control.Applicative (liftA2)
import Data.Fin            (Fin)
import Data.Functor.Apply  (Apply, liftF2)
import Data.Nat
import Data.Semigroup      (Semigroup (..))
import Data.Vec.Lazy
       (Vec (..), VecEach (..), cons, empty, head, null, reifyList, singleton,
       tail, _Cons, _head, _tail)

--- Instances
import qualified Control.Lens as I

import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert to pull 'P.Vec'.
toPull :: forall n a. N.InlineInduction n => Vec n a -> P.Vec n a
toPull = getToPull (N.inlineInduction1 start step) where
    start :: ToPull 'Z a
    start = ToPull $ \_ -> P.Vec F.absurd

    step :: ToPull m a -> ToPull ('S m) a
    step (ToPull f) = ToPull $ \(x ::: xs) -> P.Vec $ \i -> case i of
        F.Z    -> x
        F.S i' -> P.unVec (f xs) i'

newtype ToPull n a = ToPull { getToPull :: Vec n a -> P.Vec n a }

-- | Convert from pull 'P.Vec'.
fromPull :: forall n a. N.InlineInduction n => P.Vec n a -> Vec n a
fromPull = getFromPull (N.inlineInduction1 start step) where
    start :: FromPull 'Z a
    start = FromPull $ const VNil

    step :: FromPull m a -> FromPull ('S m) a
    step (FromPull f) = FromPull $ \(P.Vec v) -> v F.Z ::: f (P.Vec (v . F.S))

newtype FromPull n a = FromPull { getFromPull :: P.Vec n a -> Vec n a }

-- | An 'I.Iso' from 'toPull' and 'fromPull'.
_Pull :: N.InlineInduction n => I.Iso (Vec n a) (Vec n b) (P.Vec n a) (P.Vec n b)
_Pull = I.iso toPull fromPull

-- | Convert 'Vec' to list.
--
-- >>> toList $ 'f' ::: 'o' ::: 'o' ::: VNil
-- "foo"
toList :: forall n a. N.InlineInduction n => Vec n a -> [a]
toList = getToList (N.inlineInduction1 start step) where
    start :: ToList 'Z a
    start = ToList (const [])

    step :: ToList m a -> ToList ('S m) a
    step (ToList f) = ToList $ \(x ::: xs) -> x : f xs

newtype ToList n a = ToList { getToList :: Vec n a -> [a] }

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
fromList :: N.InlineInduction n => [a] -> Maybe (Vec n a)
fromList = getFromList (N.inlineInduction1 start step) where
    start :: FromList 'Z a
    start = FromList $ \xs -> case xs of
        []      -> Just VNil
        (_ : _) -> Nothing

    step :: FromList n a -> FromList ('N.S n) a
    step (FromList f) = FromList $ \xs -> case xs of
        []       -> Nothing
        (x : xs') -> (x :::) <$> f xs'

newtype FromList n a = FromList { getFromList :: [a] -> Maybe (Vec n a) }

-- | Prism from list.
--
-- >>> "foo" ^? _Vec :: Maybe (Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> "foo" ^? _Vec :: Maybe (Vec N.Nat2 Char)
-- Nothing
--
-- >>> _Vec # (True ::: False ::: VNil)
-- [True,False]
--
_Vec :: N.InlineInduction n => I.Prism' [a] (Vec n a)
_Vec = I.prism' toList fromList

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
fromListPrefix :: N.InlineInduction n => [a] -> Maybe (Vec n a)
fromListPrefix = getFromList (N.inlineInduction1 start step) where
    start :: FromList 'Z a
    start = FromList $ \_ -> Just VNil -- different than in fromList case

    step :: FromList n a -> FromList ('N.S n) a
    step (FromList f) = FromList $ \xs -> case xs of
        []       -> Nothing
        (x : xs') -> (x :::) <$> f xs'

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

flipIndex :: N.InlineInduction n => Fin n -> Vec n a -> a
flipIndex = getIndex (N.inlineInduction1 start step) where
    start :: Index 'Z a
    start = Index F.absurd

    step :: Index m a-> Index ('N.S m) a
    step (Index go) = Index $ \n (x ::: xs) -> case n of
        F.Z   -> x
        F.S m -> go m xs

newtype Index n a = Index { getIndex :: Fin n -> Vec n a -> a }

-- | Indexing.
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) ! F.S F.Z
-- 'b'
--
(!) :: N.InlineInduction n => Vec n a -> Fin n -> a
(!) = flip flipIndex

-- | Index lens.
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) ^. ix (F.S F.Z)
-- 'b'
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) & ix (F.S F.Z) .~ 'x'
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: N.InlineInduction n => Fin n -> I.Lens' (Vec n a) a
ix = getIxLens $ N.inlineInduction1 start step where
    start :: IxLens 'Z a
    start = IxLens F.absurd

    step :: IxLens m a -> IxLens ('S m) a
    step (IxLens l) = IxLens $ \i -> case i of
        F.Z   -> _head
        F.S j -> _tail . l j

newtype IxLens n a = IxLens { getIxLens :: Fin n -> I.Lens' (Vec n a) a }

-------------------------------------------------------------------------------
-- Concatenation
-------------------------------------------------------------------------------

infixr 5 ++

-- | Append two 'Vec'.
--
-- >>> ('a' ::: 'b' ::: VNil) ++ ('c' ::: 'd' ::: VNil)
-- 'a' ::: 'b' ::: 'c' ::: 'd' ::: VNil
--
(++) :: forall n m a. N.InlineInduction n => Vec n a -> Vec m a -> Vec (N.Plus n m) a
as ++ ys = getAppend (N.inlineInduction1 start step) as where
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
split :: N.InlineInduction n => Vec (N.Plus n m) a -> (Vec n a, Vec m a)
split = appSplit (N.inlineInduction1 start step) where
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
concatMap :: forall a b n m. (N.InlineInduction m, N.InlineInduction n) => (a -> Vec m b) -> Vec n a -> Vec (N.Mult n m) b
concatMap f = getConcatMap $ N.inlineInduction1 start step where
    start :: ConcatMap m a 'Z b
    start = ConcatMap $ \_ -> VNil

    step :: ConcatMap m a p b -> ConcatMap m a ('S p) b
    step (ConcatMap g) = ConcatMap $ \(x ::: xs) -> f x ++ g xs

newtype ConcatMap m a n b = ConcatMap { getConcatMap :: Vec n a -> Vec (N.Mult n m) b }

-- | @'concatMap' 'id'@
concat :: (N.InlineInduction m, N.InlineInduction n) => Vec n (Vec m a) -> Vec (N.Mult n m) a
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
chunks :: (N.InlineInduction n, N.InlineInduction m) => Vec (N.Mult n m) a -> Vec n (Vec m a)
chunks = getChunks $ N.induction1 start step where
    start :: Chunks m 'Z a
    start = Chunks $ \_ -> VNil

    step :: forall m n a. N.InlineInduction m => Chunks m n a -> Chunks m ('S n) a
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
map :: forall a b n. N.InlineInduction n => (a -> b) -> Vec n a -> Vec n b
map f = getMap $ N.inlineInduction1 start step where
    start :: Map a 'Z b
    start = Map $ \_ -> VNil

    step :: Map a m b -> Map a ('S m) b
    step (Map go) = Map $ \(x ::: xs) -> f x ::: go xs

newtype Map a n b = Map { getMap :: Vec n a -> Vec n b }

-- | >>> imap (,) $ 'a' ::: 'b' ::: 'c' ::: VNil
-- (0,'a') ::: (1,'b') ::: (2,'c') ::: VNil
--
imap :: N.InlineInduction n => (Fin n -> a -> b) -> Vec n a -> Vec n b
imap = getIMap $ N.inlineInduction1 start step where
    start :: IMap a 'Z b
    start = IMap $ \_ _ -> VNil

    step :: IMap a m b -> IMap a ('S m) b
    step (IMap go) = IMap $ \f (x ::: xs) -> f F.Z x ::: go (f . F.S) xs

newtype IMap a n b = IMap { getIMap :: (Fin n -> a -> b) -> Vec n a -> Vec n b }

-- | Apply an action to every element of a 'Vec', yielding a 'Vec' of results.
traverse :: forall n f a b. (Applicative f, N.InlineInduction n) => (a -> f b) -> Vec n a -> f (Vec n b)
traverse f =  getTraverse $ N.inlineInduction1 start step where
    start :: Traverse f a 'Z b
    start = Traverse $ \_ -> pure VNil

    step :: Traverse f a m b -> Traverse f a ('S m) b
    step (Traverse go) = Traverse $ \(x ::: xs) -> liftA2 (:::) (f x) (go xs)

newtype Traverse f a n b = Traverse { getTraverse :: Vec n a -> f (Vec n b) }

-- | Apply an action to non-empty 'Vec', yielding a 'Vec' of results.
traverse1 :: forall n f a b. (Apply f, N.InlineInduction n) => (a -> f b) -> Vec ('S n) a -> f (Vec ('S n) b)
traverse1 f = getTraverse1 $ N.inlineInduction1 start step where
    start :: Traverse1 f a 'Z b
    start = Traverse1 $ \(x ::: _) -> (::: VNil) <$> f x

    step :: Traverse1 f a m b -> Traverse1 f a ('S m) b
    step (Traverse1 go) = Traverse1 $ \(x ::: xs) -> liftF2 (:::) (f x) (go xs)

newtype Traverse1 f a n b = Traverse1 { getTraverse1 :: Vec ('S n) a -> f (Vec ('S n) b) }

-- | Apply an action to every element of a 'Vec' and its index, yielding a 'Vec' of results.
itraverse :: forall n f a b. (Applicative f, N.InlineInduction n) => (Fin n -> a -> f b) -> Vec n a -> f (Vec n b)
itraverse = getITraverse $ N.inlineInduction1 start step where
    start :: ITraverse f a 'Z b
    start = ITraverse $ \_ _ -> pure VNil

    step :: ITraverse f a m b -> ITraverse f a ('S m) b
    step (ITraverse go) = ITraverse $ \f (x ::: xs) -> liftA2 (:::) (f F.Z x) (go (f . F.S) xs)

newtype ITraverse f a n b = ITraverse { getITraverse :: (Fin n -> a -> f b) -> Vec n a -> f (Vec n b) }

-- | Apply an action to every element of a 'Vec' and its index, ignoring the results.
itraverse_ :: forall n f a b. (Applicative f, N.InlineInduction n) => (Fin n -> a -> f b) -> Vec n a -> f ()
itraverse_ = getITraverse_ $ N.inlineInduction1 start step where
    start :: ITraverse_ f a 'Z b
    start = ITraverse_ $ \_ _ -> pure ()

    step :: ITraverse_ f a m b -> ITraverse_ f a ('S m) b
    step (ITraverse_ go) = ITraverse_ $ \f (x ::: xs) -> f F.Z x *> go (f . F.S) xs

newtype ITraverse_ f a n b = ITraverse_ { getITraverse_ :: (Fin n -> a -> f b) -> Vec n a -> f () }

-------------------------------------------------------------------------------
-- Folding
-------------------------------------------------------------------------------

-- | See 'I.Foldable'.
foldMap :: (Monoid m, N.InlineInduction n) => (a -> m) -> Vec n a -> m
foldMap f = getFold $ N.inlineInduction1 (Fold (const mempty)) $ \(Fold go) ->
    Fold $ \(x ::: xs) -> f x `mappend` go xs

newtype Fold  a n b = Fold  { getFold  :: Vec n a -> b }

-- | See 'I.Foldable1'.
foldMap1 :: forall s a n. (Semigroup s, N.InlineInduction n) => (a -> s) -> Vec ('S n) a -> s
foldMap1 f = getFold1 $ N.inlineInduction1 start step where
    start :: Fold1 a 'Z s
    start = Fold1 $ \(x ::: _) -> f x

    step :: Fold1 a m s -> Fold1 a ('S m) s
    step (Fold1 g) = Fold1 $ \(x ::: xs) -> f x <> g xs

newtype Fold1 a n b = Fold1 { getFold1 :: Vec ('S n) a -> b }

-- | See 'I.FoldableWithIndex'.
ifoldMap :: forall a n m. (Monoid m, N.InlineInduction n) => (Fin n -> a -> m) -> Vec n a -> m
ifoldMap = getIFoldMap $ N.inlineInduction1 start step where
    start :: IFoldMap a 'Z m
    start = IFoldMap $ \_ _ -> mempty

    step :: IFoldMap a p m -> IFoldMap a ('S p) m
    step (IFoldMap go) = IFoldMap $ \f (x ::: xs) -> f F.Z x `mappend` go (f . F.S) xs

newtype IFoldMap a n m = IFoldMap { getIFoldMap :: (Fin n -> a -> m) -> Vec n a -> m }

-- | There is no type-class for this :(
ifoldMap1 :: forall a n s. (Semigroup s, N.InlineInduction n) => (Fin ('S n) -> a -> s) -> Vec ('S n) a -> s
ifoldMap1 = getIFoldMap1 $ N.inlineInduction1 start step where
    start :: IFoldMap1 a 'Z s
    start = IFoldMap1 $ \f (x ::: _) -> f F.Z x

    step :: IFoldMap1 a p s -> IFoldMap1 a ('S p) s
    step (IFoldMap1 go) = IFoldMap1 $ \f (x ::: xs) -> f F.Z x <> go (f . F.S) xs

newtype IFoldMap1 a n m = IFoldMap1 { getIFoldMap1 :: (Fin ('S n) -> a -> m) -> Vec ('S n) a -> m }

-- | Right fold.
foldr :: forall a b n. N.InlineInduction n => (a -> b -> b) -> b -> Vec n a -> b
foldr f z = getFold $ N.inlineInduction1 start step where
    start :: Fold a 'Z b
    start = Fold $ \_ -> z

    step :: Fold a m b -> Fold a ('S m) b
    step (Fold go) = Fold $ \(x ::: xs) -> f x (go xs)

-- | Right fold with an index.
ifoldr :: forall a b n. N.InlineInduction n => (Fin n -> a -> b -> b) -> b -> Vec n a -> b
ifoldr = getIFoldr $ N.inlineInduction1 start step where
    start :: IFoldr a 'Z b
    start = IFoldr $ \_ z _ -> z

    step :: IFoldr a m b -> IFoldr a ('S m) b
    step (IFoldr go) = IFoldr $ \f z (x ::: xs) -> f F.Z x (go (f . F.S) z xs)

newtype IFoldr a n b = IFoldr { getIFoldr :: (Fin n -> a -> b -> b) -> b -> Vec n a -> b }

-- | Yield the length of a 'Vec'. /O(n)/
length :: forall n a. N.InlineInduction n => Vec n a -> Int
length _ = getLength l where
    l :: Length n
    l = N.inlineInduction (Length 0) $ \(Length n) -> Length (1 + n)

newtype Length (n :: Nat) = Length { getLength :: Int }

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- | Non-strict 'sum'.
sum :: (Num a, N.InlineInduction n) => Vec n a -> a
sum = getFold $ N.inlineInduction1 start step where
    start :: Num a => Fold a 'Z a
    start = Fold $ \_ -> 0

    step :: Num a => Fold a m a -> Fold a ('S m) a
    step (Fold f) = Fold $ \(x ::: xs) -> x + f xs

-- | Non-strict 'product'.
product :: (Num a, N.InlineInduction n) => Vec n a -> a
product = getFold $ N.inlineInduction1 start step where
    start :: Num a => Fold a 'Z a
    start = Fold $ \_ -> 0

    step :: Num a => Fold a m a -> Fold a ('S m) a
    step (Fold f) = Fold $ \(x ::: xs) -> x + f xs

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'Vec's with a function.
zipWith :: forall a b c n. N.InlineInduction n => (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f = getZipWith $ N.inlineInduction start step where
    start :: ZipWith a b c 'Z
    start = ZipWith $ \_ _ -> VNil

    step :: ZipWith a b c m -> ZipWith a b c ('S m)
    step (ZipWith go) = ZipWith $ \(x ::: xs) (y ::: ys) -> f x y ::: go xs ys

newtype ZipWith a b c n = ZipWith { getZipWith :: Vec n a -> Vec n b -> Vec n c }

-- | Zip two 'Vec's. with a function that also takes the elements' indices.
izipWith :: N.InlineInduction n => (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
izipWith = getIZipWith $ N.inlineInduction start step where
    start :: IZipWith a b c 'Z
    start = IZipWith $ \_ _ _ -> VNil

    step :: IZipWith a b c m -> IZipWith a b c ('S m)
    step (IZipWith go) = IZipWith $ \f (x ::: xs) (y ::: ys) -> f F.Z x y ::: go (f . F.S) xs ys

newtype IZipWith a b c n = IZipWith { getIZipWith :: (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c }

-------------------------------------------------------------------------------
-- Monadic
-------------------------------------------------------------------------------

-- | Monadic bind.
bind :: N.InlineInduction n => Vec n a -> (a -> Vec n b) -> Vec n b
bind = getBind $ N.inlineInduction1 start step where
    start :: Bind a 'Z b
    start = Bind $ \_ _ -> VNil

    step :: Bind a m b -> Bind a ('S m) b
    step (Bind go) = Bind $ \(x ::: xs) f -> head (f x) ::: go xs (tail . f)

newtype Bind a n b = Bind { getBind :: Vec n a -> (a -> Vec n b) -> Vec n b }

-- | Monadic join.
--
-- >>> join $ ('a' ::: 'b' ::: VNil) ::: ('c' ::: 'd' ::: VNil) ::: VNil
-- 'a' ::: 'd' ::: VNil
join :: N.InlineInduction n => Vec n (Vec n a) -> Vec n a
join = getJoin $ N.inlineInduction1 start step where
    start :: Join 'Z a
    start = Join $ \_ -> VNil

    step :: N.InlineInduction m => Join m a -> Join ('S m) a
    step (Join go) = Join $ \(x ::: xs) -> head x ::: go (map tail xs)

newtype Join n a = Join { getJoin :: Vec n (Vec n a) -> Vec n a }

-------------------------------------------------------------------------------
-- universe
-------------------------------------------------------------------------------

-- | Get all @'Fin' n@ in a @'Vec' n@.
--
-- >>> universe :: Vec N.Nat3 (Fin N.Nat3)
-- 0 ::: 1 ::: 2 ::: VNil
universe :: N.InlineInduction n => Vec n (Fin n)
universe = getUniverse (N.inlineInduction first step) where
    first :: Universe 'Z
    first = Universe VNil

    step :: N.InlineInduction m => Universe m -> Universe ('S m)
    step (Universe go) = Universe (F.Z ::: map F.S go)

newtype Universe n = Universe { getUniverse :: Vec n (Fin n) }

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Lens ((^.), (&), (.~), (^?), (#))
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Prelude.Compat (Char, Bool (..), not, uncurry)
