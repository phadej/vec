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
-- | Length-indexed random access list.
--
-- See <http://www.staff.science.uu.nl/~swier004/publications/2019-jfp-submission.pdf>
module Data.RAVec (
    -- * Random access list
    RAVec (..),

    -- * Construction
    empty,
    singleton,
    cons,
    withCons,
    head,
    last,

    -- * Conversion
    toList,
    toNonEmpty,
    fromList,
    reifyNonEmpty,

    -- * Indexing
    (!),
    tabulate,

    -- * Folds
    foldMap,
    foldMap1,
    ifoldMap,
    ifoldMap1,
    foldr,
    ifoldr,

    -- * Mapping
    map,
    imap,
    traverse,
    itraverse,
#ifdef MIN_VERSION_semigroupoids
    traverse1,
    itraverse1,
#endif

    -- * Zipping
    zipWith,
    izipWith,

    -- * Universe
    universe,
    repeat,

    -- * QuickCheck
    liftArbitrary,
    liftShrink,
    )  where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Maybe (..), Ord (..), Show, ($), (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Data.Bin            (Bin (..))
import Data.Bin.Pos        (Pos (..))
import Data.Hashable       (Hashable (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Monoid         (Monoid (..))
import Data.Semigroup      (Semigroup (..))
import Data.Type.Bin       (SBin (..), SBinI (..), SBinPI (..))
import Data.Type.Equality  ((:~:) (..))
import Data.Typeable       (Typeable)

import qualified Data.RAVec.NonEmpty as NE
import qualified Data.Type.Bin       as B

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

import Data.RAVec.NonEmpty (NERAVec (..))

-- $setup
-- >>> :set -XScopedTypeVariables -XDataKinds
-- >>> import Prelude (print, Char, Bounded (..))
-- >>> import Data.List (sort)
-- >>> import Data.Wrd (Wrd (..))
-- >>> import Data.Bin.Pos (top, pop)
-- >>> import Data.BinP.PosP (PosP (..), PosP' (..))
-- >>> import qualified Data.Bin.Pos as P

-------------------------------------------------------------------------------
-- Random access vec
-------------------------------------------------------------------------------

-- | Length indexed random access lists.
data RAVec (b :: Bin) a where
    Empty    :: RAVec 'BZ a
    NonEmpty :: NERAVec b a -> RAVec ('BP b) a
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq a   => Eq   (RAVec b a)
deriving instance Show a => Show (RAVec b a)

instance Ord a => Ord (RAVec b a) where
    compare xs ys = compare (toList xs) (toList ys)

instance Functor (RAVec b) where
    fmap = map

instance I.Foldable (RAVec b) where
    foldMap    = foldMap
    foldr      = foldr

#if MIN_VERSION_base(4,8,0)
    null = null
#endif

instance I.Traversable (RAVec b) where
    traverse = traverse

-- | @since 0.2
instance WI.FunctorWithIndex (Pos n) (RAVec n) where
    imap = imap

-- | @since 0.2
instance WI.FoldableWithIndex (Pos n) (RAVec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

-- | @since 0.2
instance WI.TraversableWithIndex (Pos n) (RAVec n) where
    itraverse = itraverse

#ifdef MIN_VERSION_semigroupoids
instance b ~ 'BP n => I.Foldable1 (RAVec b) where
    foldMap1   = foldMap1
    toNonEmpty = toNonEmpty

instance b ~ 'BP n => I.Traversable1 (RAVec b) where
    traverse1 = traverse1
#endif

instance NFData a => NFData (RAVec b a) where
    rnf Empty          = ()
    rnf (NonEmpty ral) = rnf ral

instance Hashable a => Hashable (RAVec b a) where
    hashWithSalt salt = hashWithSalt salt . toList

instance SBinI b => Applicative (RAVec b) where
    pure   = repeat
    (<*>)  = zipWith ($)
    x <* _ = x
    _ *> x = x
#if MIN_VERSION_base(4,10,0)
    liftA2 = zipWith
#endif

-- TODO: Monad?

#ifdef MIN_VERSION_distributive
instance SBinI b => I.Distributive (RAVec b) where
    distribute f = tabulate (\k -> fmap (! k) f)

#ifdef MIN_VERSION_adjunctions
instance SBinI b => I.Representable (RAVec b) where
    type Rep (RAVec b) = Pos b
    index    = (!)
    tabulate = tabulate

#endif
#endif

instance Semigroup a => Semigroup (RAVec b a) where
    (<>) = zipWith (<>)

instance (Monoid a, SBinI b) => Monoid (RAVec b a) where
    mempty  = repeat mempty
    mappend = zipWith mappend

#ifdef MIN_VERSION_semigroupoids
instance Apply (RAVec b) where
    (<.>) = zipWith ($)
    liftF2 = zipWith
    _ .> x = x
    x <. _ = x
#endif

-- TODO: I.Bind?

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty :: RAVec B.Bin0 a
empty = Empty

singleton :: a -> RAVec B.Bin1 a
singleton = NonEmpty . NE.singleton

-- | Cons an element in front of 'RAVec'.
--
-- >>> reifyList "xyz" (print . toList . cons 'a')
-- "axyz"
--
cons :: a -> RAVec b a -> RAVec (B.Succ b) a
cons x Empty         = singleton x
cons x (NonEmpty xs) = NonEmpty (NE.cons x xs)

-- | Variant of 'cons' which computes the 'SBinI' dictionary at the same time.
withCons :: SBinI b => a -> RAVec b a -> (SBinPI (B.Succ' b) => RAVec (B.Succ b) a -> r) -> r
withCons = go sbin where
    go :: SBin b -> a -> RAVec b a -> (SBinPI (B.Succ' b) => RAVec (B.Succ b) a -> r) -> r
    go SBZ x Empty k         = k (singleton x)
    go SBP x (NonEmpty xs) k = NE.withCons x xs $ k . NonEmpty

-- | The first element of a non-empty 'RAVec'.
--
-- >>> reifyNonEmpty ('x' :| "yz") head
-- 'x'
--
head :: RAVec ('BP b) a -> a
head (NonEmpty ral) = NE.head ral

-- | The last element of a non-empty 'RAVec'.
--
-- >>> reifyNonEmpty ('x' :| "yz") last
-- 'z'
--
last :: RAVec ('BP b) a -> a
last (NonEmpty ral) = NE.last ral

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toList :: RAVec b a -> [a]
toList Empty          = []
toList (NonEmpty ral) = NE.toList ral

toNonEmpty :: RAVec ('BP b) a -> NonEmpty a
toNonEmpty (NonEmpty ral) = NE.toNonEmpty ral

-- | Convert a list @[a]@ to @'RAVec' b a@.
-- Returns 'Nothing' if lengths don't match.
--
-- >>> fromList "foo" :: Maybe (RAVec B.Bin3 Char)
-- Just (NonEmpty (NE (Cons1 (Leaf 'f') (Last (Node (Leaf 'o') (Leaf 'o'))))))
--
-- >>> fromList "quux" :: Maybe (RAVec B.Bin3 Char)
-- Nothing
--
-- >>> fromList "xy" :: Maybe (RAVec B.Bin3 Char)
-- Nothing
--
fromList :: forall b a. SBinI b => [a] -> Maybe (RAVec b a)
fromList xs = reifyList xs mk where
    mk :: forall c. SBinI c => RAVec c a -> Maybe (RAVec b a)
    mk ral = do
        Refl <- B.eqBin :: Maybe (b :~: c)
        Just ral

-- |
--
-- >>> reifyList "foo" print
-- NonEmpty (NE (Cons1 (Leaf 'f') (Last (Node (Leaf 'o') (Leaf 'o')))))
--
-- >>> reifyList "xyzzy" toList
-- "xyzzy"
reifyList :: [a] -> (forall b. SBinI b => RAVec b a -> r) -> r
reifyList []     k = k Empty
reifyList (x:xs) k = reifyList xs $ \ral -> withCons x ral k

reifyNonEmpty :: NonEmpty a -> (forall b. SBinPI b => RAVec ('BP b) a -> r) -> r
reifyNonEmpty xs k = NE.reifyNonEmpty xs $ k . NonEmpty

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing.
--
-- >>> let ral :: RAVec B.Bin4 Char; Just ral = fromList "abcd"
--
-- >>> ral ! minBound
-- 'a'
--
-- >>> ral ! maxBound
-- 'd'
--
-- >>> ral ! pop top
-- 'b'
--
(!) :: RAVec b a -> Pos b -> a
(!) Empty        p       = case p of {}
(!) (NonEmpty b) (Pos i) = b NE.! i

tabulate :: forall b a. SBinI b => (Pos b -> a) -> RAVec b a
tabulate f = case sbin :: SBin b of
    SBZ -> Empty
    SBP -> NonEmpty (NE.tabulate (f . Pos))

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldMap :: Monoid m => (a -> m) -> RAVec n a -> m
foldMap _ Empty        = mempty
foldMap f (NonEmpty r) = NE.foldMap f r

ifoldMap :: Monoid m => (Pos b -> a -> m) -> RAVec b a -> m
ifoldMap _ Empty        = mempty
ifoldMap f (NonEmpty r) = NE.ifoldMap (f . Pos) r

foldMap1 :: Semigroup m => (a -> m) -> RAVec ('BP b) a -> m
foldMap1 f (NonEmpty r) = NE.foldMap1 f r

ifoldMap1 :: Semigroup m => (Pos ('BP b) -> a -> m) -> RAVec ('BP b) a -> m
ifoldMap1 f (NonEmpty r) = NE.ifoldMap1 (f . Pos) r

foldr :: (a -> b -> b) -> b -> RAVec n a -> b
foldr _ z Empty          = z
foldr f z (NonEmpty ral) = NE.foldr f z ral

ifoldr :: (Pos n -> a -> b -> b) -> b -> RAVec n a -> b
ifoldr _ z Empty          = z
ifoldr f z (NonEmpty ral) = NE.ifoldr (f . Pos) z ral

null :: RAVec n a -> Bool
null Empty        = True
null (NonEmpty _) = False

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- TBW

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

map :: (a -> b) -> RAVec n a -> RAVec n b
map _ Empty        = Empty
map f (NonEmpty r) = NonEmpty (NE.map f r)

imap :: (Pos n -> a -> b) -> RAVec n a -> RAVec n b
imap _ Empty = Empty
imap f (NonEmpty r) = NonEmpty (NE.imap (f . Pos) r)

traverse :: Applicative f => (a -> f b) -> RAVec n a -> f (RAVec n b)
traverse _ Empty          = pure empty
traverse f (NonEmpty ral) = NonEmpty <$> NE.traverse f ral

itraverse :: Applicative f => (Pos n -> a -> f b) -> RAVec n a -> f (RAVec n b)
itraverse _ Empty        = pure Empty
itraverse f (NonEmpty r) = NonEmpty <$> NE.itraverse (f . Pos) r

#ifdef MIN_VERSION_semigroupoids
traverse1 :: Apply f => (a -> f b) -> RAVec ('BP n) a -> f (RAVec ('BP n) b)
traverse1 f (NonEmpty r) = NonEmpty <$> NE.traverse1 f r

itraverse1 :: Apply f => (Pos ('BP n) -> a -> f b) -> RAVec ('BP n) a -> f (RAVec ('BP n) b)
itraverse1 f (NonEmpty r) = NonEmpty <$> NE.itraverse1 (f . Pos) r
#endif

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'RAVec's with a function.
zipWith :: (a -> b -> c) -> RAVec n a -> RAVec n b -> RAVec n c
zipWith _ Empty         Empty         = Empty
zipWith f (NonEmpty xs) (NonEmpty ys) = NonEmpty (NE.zipWith f xs ys)

-- | Zip two 'RAVec's with a function which also takes 'Pos' index.
izipWith :: (Pos n -> a -> b -> c) -> RAVec n a -> RAVec n b -> RAVec n c
izipWith _ Empty         Empty         = Empty
izipWith f (NonEmpty xs) (NonEmpty ys) = NonEmpty (NE.izipWith (f . Pos) xs ys)

-- | Repeat a value.
--
-- >>> repeat 'x' :: RAVec B.Bin5 Char
-- NonEmpty (NE (Cons1 (Leaf 'x') (Cons0 (Last (Node (Node (Leaf 'x') (Leaf 'x')) (Node (Leaf 'x') (Leaf 'x')))))))
--
repeat :: forall b a. SBinI b => a -> RAVec b a
repeat x = case sbin :: SBin b of
    SBZ -> Empty
    SBP -> NonEmpty (NE.repeat x)

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- |
--
-- >>> universe :: RAVec B.Bin2 (Pos B.Bin2)
-- NonEmpty (NE (Cons0 (Last (Node (Leaf 0) (Leaf 1)))))
--
-- >>> let u = universe :: RAVec B.Bin3 (Pos B.Bin3)
-- >>> u
-- NonEmpty (NE (Cons1 (Leaf 0) (Last (Node (Leaf 1) (Leaf 2)))))
--
-- >>> P.explicitShow $ u ! Pos (PosP (Here WE))
-- "Pos (PosP (Here WE))"
--
-- >>> let u' = universe :: RAVec B.Bin5 (Pos B.Bin5)
--
-- >>> toList u' == sort (toList u')
-- True
--
universe :: forall b. SBinI b => RAVec b (Pos b)
universe = case sbin :: SBin b of
    SBZ -> Empty
    SBP -> NonEmpty (fmap Pos NE.universe)

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

liftArbitrary :: B.SBinI b => QC.Gen a -> QC.Gen (RAVec b a)
liftArbitrary = liftArbitrary

liftShrink :: (a -> [a]) -> RAVec b a -> [RAVec b a]
liftShrink _   Empty        = []
liftShrink shr (NonEmpty r) = NonEmpty <$> NE.liftShrink shr r

instance B.SBinI b => QC.Arbitrary1 (RAVec b) where
    liftArbitrary = liftArbitrary
    liftShrink    = liftShrink

instance (B.SBinI b, QC.Arbitrary a) => QC.Arbitrary (RAVec b a) where
    arbitrary = QC.arbitrary1
    shrink    = QC.shrink1

instance QC.CoArbitrary a => QC.CoArbitrary (RAVec b a) where
    coarbitrary Empty        = QC.variant (0 :: Int)
    coarbitrary (NonEmpty r) = QC.variant (1 :: Int) . QC.coarbitrary r

instance (B.SBinI b, QC.Function a) => QC.Function (RAVec b a) where
    function = case B.sbin :: B.SBin b of
        SBZ -> QC.functionMap (\Empty -> ())       (\() -> Empty) 
        SBP -> QC.functionMap (\(NonEmpty r) -> r) NonEmpty
