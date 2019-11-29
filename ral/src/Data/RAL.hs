{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
-- | Length-indexed random access list.
--
-- See <http://www.staff.science.uu.nl/~swier004/publications/2019-jfp-submission.pdf>
module Data.RAL (
    -- * Random access list
    RAL (..),
    NERAL (..),

    -- * Construction
    empty,
    singleton,
    singletonNE,
    cons,
    consNE,
    withCons,
    withConsNE,
    head,
    headNE,
    last,
    lastNE,

    -- * Conversion
    toList,
    fromList,
    toListNE,
    reifyList,
    reifyNonEmpty,

    -- * Indexing
    (!),
    indexNE,

    -- * Folds
    foldMap,
    foldMapNE,
    foldMap1,
    foldMap1NE,
    ifoldMap,
    ifoldMapNE,
    ifoldMap1,
    ifoldMap1NE,
    foldr,
    foldrNE,
    ifoldr,
    ifoldrNE,

    -- * Mapping
    map,
    mapNE,
    imap,
    imapNE,
    traverse,
    traverseNE,
    traverse1,
    traverse1NE,
    itraverse,
    itraverseNE,
    itraverse1,
    itraverse1NE,

    -- * Zipping
    zipWith,
    zipWithNE,
    izipWith,
    izipWithNE,

    -- * Universe
    universe,
    )  where

import Prelude
       (Bool (..), Eq (..), Functor (..), Maybe (..), Ord (..), Show, seq, ($),
       (.))

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq     (NFData (..))
import Data.Bin            (Bin (..), BinN (..))
import Data.Distributive   (Distributive (..))
import Data.Functor.Apply  (Apply (..))
import Data.Functor.Rep    (Representable (..), distributeRep)
import Data.Hashable       (Hashable (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Semigroup      (Semigroup (..))
import Data.Type.Equality  ((:~:) (..))
import Data.Typeable       (Typeable)

import qualified Data.RAL.Tree as Tree
import qualified Data.Type.Nat as N

import qualified Control.Lens               as L
import qualified Data.Foldable              as I (Foldable (..))
import qualified Data.Semigroup.Foldable    as I (Foldable1 (..))
import qualified Data.Semigroup.Traversable as I (Traversable1 (..))
import qualified Data.Traversable           as I (Traversable (..))

import Data.RAL.Pos
import Data.RAL.Tree (Tree (..))
import Data.Type.Bin

-- $setup
-- >>> :set -XScopedTypeVariables -XDataKinds
-- >>> import Prelude (print, Char, Bounded (..))
-- >>> import Control.Lens ((^.), (&), (.~), (^?), (#))
-- >>> import Data.Vec.Lazy (Vec (..))
-- >>> import Data.List (sort)

-------------------------------------------------------------------------------
-- Random access list
-------------------------------------------------------------------------------

-- | Length indexed random access lists.
data RAL (b :: Bin) a where
    Empty    :: RAL 'BZ a
    NonEmpty :: NERAL 'Z b a -> RAL ('BN b) a
  deriving (Typeable)

-- | Non-empty random access list.
data NERAL (n :: Nat) (b :: BinN) a where
    Last   :: Tree n a -> NERAL n 'BE a
    Cons0 ::             NERAL ('S n) b a -> NERAL n ('B0 b) a
    Cons1 :: Tree n a -> NERAL ('S n) b a -> NERAL n ('B1 b) a
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq a   => Eq   (RAL b a)
deriving instance Show a => Show (RAL b a)

deriving instance Eq a   => Eq   (NERAL n b a)
deriving instance Show a => Show (NERAL n b a)

instance Ord a => Ord (RAL b a) where
    compare xs ys = compare (toList xs) (toList ys)

instance Ord a => Ord (NERAL n b a) where
    compare xs ys = compare (toListNE xs) (toListNE ys)

instance Functor (RAL b) where
    fmap = map

instance Functor (NERAL n b) where
    fmap = mapNE

instance I.Foldable (RAL b) where
    foldMap = foldMap
    foldr   = foldr

#if MIN_VERSION_base(4,8,0)
    null = null
#endif

instance I.Foldable (NERAL n b) where
    foldMap = foldMapNE
    foldr   = foldrNE

#if MIN_VERSION_base(4,8,0)
    null _ = False
#endif

instance b ~ 'BN n => I.Foldable1 (RAL b) where
    foldMap1 = foldMap1

instance I.Foldable1 (NERAL n b) where
    foldMap1 = foldMap1NE

instance I.Traversable (RAL b) where
    traverse = traverse

instance I.Traversable (NERAL n b) where
    traverse = traverseNE

instance b ~ 'BN n => I.Traversable1 (RAL b) where
    traverse1 = traverse1

instance I.Traversable1 (NERAL n b) where
    traverse1 = traverse1NE

instance NFData a => NFData (RAL b a) where
    rnf Empty          = ()
    rnf (NonEmpty ral) = rnf ral

instance NFData a => NFData (NERAL n b a) where
    rnf (Last  t)   = rnf t
    rnf (Cons0   r) = rnf r
    rnf (Cons1 t r) = rnf t `seq` rnf r

instance Hashable a => Hashable (RAL b a) where
    hashWithSalt salt = hashWithSalt salt . toList

instance Hashable a => Hashable (NERAL n b a) where
    hashWithSalt salt = hashWithSalt salt . toListNE

instance SBinI b => Applicative (RAL b) where
    pure   = repeat
    (<*>)  = (<.>)
    (<*)   = (<.)
    (*>)   = (.>)
#if MIN_VERSION_base(4,10,0)
    liftA2 = liftF2
#endif

instance (SBinNI b, N.SNatI n) => Applicative (NERAL n b) where
    pure   = repeatNE
    (<*>)  = (<.>)
    (<*)   = (<.)
    (*>)   = (.>)
#if MIN_VERSION_base(4,10,0)
    liftA2 = liftF2
#endif

-- TODO: Monad?

instance SBinI b => Distributive (RAL b) where
    distribute = distributeRep

instance (SBinNI b, N.SNatI n) => Distributive (NERAL n b) where
    distribute = distributeRep

instance SBinI b => Representable (RAL b) where
    type Rep (RAL b) = Pos b
    index = (!)
    tabulate f = case sbin :: SBin b of
        SBZ -> Empty
        SBN -> NonEmpty (tabulate (f . Pos))

instance (SBinNI b, N.SNatI n) => Representable (NERAL n b) where
    type Rep (NERAL n b) = PosN n b
    index = indexNE

    tabulate f = case sbinN :: SBinN b of
        SBE -> Last (tabulate (f . AtEnd))
        SB0 -> Cons0 (tabulate (f . There0))
        SB1 -> Cons1 (tabulate (f . Here)) (tabulate (f . There1))

instance Semigroup a => Semigroup (RAL b a) where
    (<>) = zipWith (<>)

instance Semigroup a => Semigroup (NERAL n b a) where
    (<>) = zipWithNE (<>)

instance (Monoid a, SBinI b) => Monoid (RAL b a) where
    mempty  = repeat mempty
    mappend = zipWith mappend

instance (Monoid a, SBinNI b, N.SNatI n) => Monoid (NERAL n b a) where
    mempty  = repeatNE mempty
    mappend = zipWithNE mappend

instance Apply (RAL b) where
    (<.>) = zipWith ($)
    liftF2 = zipWith
    _ .> x = x
    x <. _ = x

instance Apply (NERAL n b) where
    (<.>) = zipWithNE ($)
    liftF2 = zipWithNE
    _ .> x = x
    x <. _ = x

-- TODO: I.Bind?

instance L.FunctorWithIndex (Pos b) (RAL b) where
    imap = imap

instance L.FunctorWithIndex (PosN n b) (NERAL n b) where
    imap = imapNE

instance L.FoldableWithIndex (Pos b) (RAL b) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.FoldableWithIndex (PosN n b) (NERAL n b) where
    ifoldMap = ifoldMapNE
    ifoldr   = ifoldrNE

instance L.TraversableWithIndex (Pos b) (RAL b) where
    itraverse = itraverse

instance L.TraversableWithIndex (PosN n b) (NERAL n b) where
    itraverse = itraverseNE

instance L.Each (RAL n a) (RAL n b) a b where
    each = traverse

instance L.Each (NERAL n m a) (NERAL n m b) a b where
    each = traverseNE

type instance L.Index   (RAL n a) = Pos n
type instance L.IxValue (RAL n a) = a

type instance L.Index   (NERAL n b a) = PosN n b
type instance L.IxValue (NERAL n b a) = a

instance L.Ixed (RAL b a) where
    ix = ix

instance L.Ixed (NERAL n b a) where
    ix = ixNE

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty :: RAL Bin0 a
empty = Empty

singleton :: a -> RAL Bin1 a
singleton = NonEmpty . singletonNE

singletonNE :: a -> NERAL 'Z BinN1 a
singletonNE = Last . Tree.singleton

-- | Cons an element in front of 'RAL'.
--
-- >>> reifyList "xyz" (print . toList . cons 'a')
-- "axyz"
--
cons :: a -> RAL b a -> RAL (Succ b) a
cons x Empty         = singleton x
cons x (NonEmpty xs) = NonEmpty (consNE x xs)

-- | 'cons' for non-empty rals.
consNE :: a -> NERAL 'Z b a -> NERAL 'Z (SuccN' b) a
consNE x = consTree (Leaf x)

consTree :: Tree n a -> NERAL n b a -> NERAL n (SuccN' b) a
consTree x (Last t)     = Cons0 (Last (Node x t))
consTree x (Cons0 r)   = Cons1 x r
consTree x (Cons1 t r) = Cons0 (consTree (Node x t) r)

-- | Variant of 'cons' which computes the 'SBinI' dictionary at the same time.
withCons :: SBinI b => a -> RAL b a -> (SBinNI (Succ' b) => RAL (Succ b) a -> r) -> r
withCons = go sbin where
    go :: SBin b -> a -> RAL b a -> (SBinNI (Succ' b) => RAL (Succ b) a -> r) -> r
    go SBZ x Empty k         = k (singleton x)
    go SBN x (NonEmpty xs) k = withConsNE x xs $ k . NonEmpty

-- | 'withCons' for non-empty rals.
withConsNE :: SBinNI b => a -> NERAL 'Z b a -> (SBinNI (SuccN' b) => NERAL 'Z (SuccN' b) a -> r) -> r
withConsNE x = withConsTree sbinN (Leaf x)

withConsTree :: SBinN b -> Tree n a -> NERAL n b a -> (SBinNI (SuccN' b) => NERAL n (SuccN' b) a -> r) -> r
withConsTree SBE x (Last t)     k = k (Cons0 (Last (Node x t)))
withConsTree SB0 x (Cons0 r)   k = k (Cons1 x r)
withConsTree SB1 x (Cons1 t r) k = withConsTree sbinN (Node x t) r $ k . Cons0

-- | The first element of a non-empty 'RAL'.
--
-- >>> reifyNonEmpty ('x' :| "yz") head
-- 'x'
--
head :: RAL ('BN b) a -> a
head (NonEmpty ral) = headNE ral

headNE :: NERAL n b a -> a
headNE (Last t)     = Tree.leftmost t
headNE (Cons0 ral) = headNE ral
headNE (Cons1 t _) = Tree.leftmost t

-- | The last element of a non-empty 'RAL'.
--
-- >>> reifyNonEmpty ('x' :| "yz") last
-- 'z'
--
last :: RAL ('BN b) a -> a
last (NonEmpty ral) = lastNE ral

lastNE :: NERAL n b a -> a
lastNE (Last t)       = Tree.rightmost t
lastNE (Cons0 ral)   = headNE ral
lastNE (Cons1 _ ral) = lastNE ral

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toList :: RAL b a -> [a]
toList Empty          = []
toList (NonEmpty ral) = toListNE ral

toListNE :: NERAL n b a -> [a]
toListNE = foldrNE (:) []

-- | Convert a list @[a]@ to @'RAL' b a@.
-- Returns 'Nothing' if lengths don't match.
--
-- >>> fromList "foo" :: Maybe (RAL Bin3 Char)
-- Just (NonEmpty (Cons1 (Leaf 'f') (Last (Node (Leaf 'o') (Leaf 'o')))))
--
-- >>> fromList "quux" :: Maybe (RAL Bin3 Char)
-- Nothing
--
-- >>> fromList "xy" :: Maybe (RAL Bin3 Char)
-- Nothing
--
fromList :: forall b a. SBinI b => [a] -> Maybe (RAL b a)
fromList xs = reifyList xs mk where
    mk :: forall c. SBinI c => RAL c a -> Maybe (RAL b a)
    mk ral = do
        Refl <- eqBin :: Maybe (b :~: c)
        Just ral

-- |
--
-- >>> reifyList "foo" print
-- NonEmpty (Cons1 (Leaf 'f') (Last (Node (Leaf 'o') (Leaf 'o'))))
--
-- >>> reifyList "xyzzy" toList
-- "xyzzy"
reifyList :: [a] -> (forall b. SBinI b => RAL b a -> r) -> r
reifyList []     k = k Empty
reifyList (x:xs) k = reifyList xs $ \ral -> withCons x ral k

reifyNonEmpty :: NonEmpty a -> (forall b. SBinNI b => RAL ('BN b) a -> r) -> r
reifyNonEmpty (x :| xs) k = reifyList xs $ \ral -> withCons x ral k

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing.
--
-- >>> let ral :: RAL Bin4 Char; Just ral = fromList "abcd"
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
(!) :: RAL b a -> Pos b -> a
(!) Empty        p       = case p of {}
(!) (NonEmpty b) (Pos i) = indexNE b i

indexNE :: NERAL n b a -> PosN n b -> a
indexNE (Last t)      (AtEnd i)  = t Tree.! i
indexNE (Cons0 ral)   (There0 i) = indexNE ral i
indexNE (Cons1 t _)   (Here i)   = t Tree.! i
indexNE (Cons1 _ ral) (There1 i) = indexNE ral i

-- | Index lens.
--
-- >>> let Just ral = fromList "xyz" :: Maybe (RAL Bin3 Char)
-- >>> ral & ix maxBound .~ 'Z'
-- NonEmpty (Cons1 (Leaf 'x') (Last (Node (Leaf 'y') (Leaf 'Z'))))
ix :: Pos b -> L.Lens' (RAL b a) a
ix (Pos n) f (NonEmpty x) = NonEmpty <$> ixNE n f x

ixNE :: PosN n b -> L.Lens' (NERAL n b a) a
ixNE (AtEnd i)  f (Last  t)   = Last <$> Tree.ix i f t
ixNE (There0 i) f (Cons0   r) = Cons0 <$> ixNE i f r
ixNE (There1 i) f (Cons1 t r) = (t `Cons1`) <$> ixNE i f r
ixNE (Here i)   f (Cons1 t r) = (`Cons1` r) <$> Tree.ix i f t

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldMap :: Monoid m => (a -> m) -> RAL n a -> m
foldMap _ Empty        = mempty
foldMap f (NonEmpty r) = foldMapNE f r

foldMapNE :: Monoid m => (a -> m) -> NERAL n b a -> m
foldMapNE f (Last  t)   = Tree.foldMap f t
foldMapNE f (Cons0   r) = foldMapNE f r
foldMapNE f (Cons1 t r) = mappend (Tree.foldMap f t) (foldMapNE f r)

ifoldMap :: Monoid m => (Pos b -> a -> m) -> RAL b a -> m
ifoldMap _ Empty        = mempty
ifoldMap f (NonEmpty r) = ifoldMapNE (f . Pos) r

ifoldMapNE :: Monoid m => (PosN n b -> a -> m) -> NERAL n b a -> m
ifoldMapNE f (Last  t)   = Tree.ifoldMap (f . AtEnd) t
ifoldMapNE f (Cons0   r) = ifoldMapNE (f . There0) r
ifoldMapNE f (Cons1 t r) = Tree.ifoldMap (f . Here) t `mappend` ifoldMapNE (f . There1) r

foldMap1 :: Semigroup m => (a -> m) -> RAL ('BN b) a -> m
foldMap1 f (NonEmpty r) = foldMap1NE f r

foldMap1NE :: Semigroup m => (a -> m) -> NERAL n b a -> m
foldMap1NE f (Last  t)   = Tree.foldMap1 f t
foldMap1NE f (Cons0   r) = foldMap1NE f r
foldMap1NE f (Cons1 t r) = Tree.foldMap1 f t <> foldMap1NE f r

ifoldMap1 :: Semigroup m => (Pos ('BN b) -> a -> m) -> RAL ('BN b) a -> m
ifoldMap1 f (NonEmpty r) = ifoldMap1NE (f . Pos) r

ifoldMap1NE :: Semigroup m => (PosN n b -> a -> m) -> NERAL n b a -> m
ifoldMap1NE f (Last  t)   = Tree.ifoldMap1 (f . AtEnd) t
ifoldMap1NE f (Cons0   r) = ifoldMap1NE (f . There0) r
ifoldMap1NE f (Cons1 t r) = Tree.ifoldMap1 (f . Here) t <> ifoldMap1NE (f . There1) r

foldr :: (a -> b -> b) -> b -> RAL n a -> b
foldr _ z Empty          = z
foldr f z (NonEmpty ral) = foldrNE f z ral

foldrNE :: (a -> b -> b) -> b -> NERAL n m a -> b
foldrNE f z (Last  t)   = Tree.foldr f z t
foldrNE f z (Cons0   r) = foldrNE f z r
foldrNE f z (Cons1 t r) = Tree.foldr f (foldrNE f z r) t

ifoldr :: (Pos n -> a -> b -> b) -> b -> RAL n a -> b
ifoldr _ z Empty          = z
ifoldr f z (NonEmpty ral) = ifoldrNE (f . Pos) z ral

ifoldrNE :: (PosN n m -> a -> b -> b) -> b -> NERAL n m a -> b
ifoldrNE f z (Last  t)   = Tree.ifoldr (f . AtEnd) z t
ifoldrNE f z (Cons0   r) = ifoldrNE (f . There0) z r
ifoldrNE f z (Cons1 t r) = Tree.ifoldr (f . Here) (ifoldrNE (f . There1) z r) t

null :: RAL n a -> Bool
null Empty        = True
null (NonEmpty _) = False

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- TBW

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

map :: (a -> b) -> RAL n a -> RAL n b
map _ Empty        = Empty
map f (NonEmpty r) = NonEmpty (mapNE f r)

mapNE :: (a -> b) -> NERAL n m a -> NERAL n m b
mapNE f (Last   t ) = Last (Tree.map f t)
mapNE f (Cons0   r) = Cons0 (mapNE f r)
mapNE f (Cons1 t r) = Cons1 (Tree.map f t) (mapNE f r)

imap :: (Pos n -> a -> b) -> RAL n a -> RAL n b
imap _ Empty = Empty
imap f (NonEmpty r) = NonEmpty (imapNE (f . Pos) r)

imapNE :: (PosN n m -> a -> b) -> NERAL n m a -> NERAL n m b
imapNE f (Last  t)   = Last (Tree.imap (f . AtEnd) t)
imapNE f (Cons0   r) = Cons0 (imapNE (f . There0) r)
imapNE f (Cons1 t r) = Cons1 (Tree.imap (f . Here) t) (imapNE (f . There1) r)

traverse :: Applicative f => (a -> f b) -> RAL n a -> f (RAL n b)
traverse _ Empty          = pure empty
traverse f (NonEmpty ral) = NonEmpty <$> traverseNE f ral

traverseNE :: Applicative f => (a -> f b) -> NERAL n m a -> f (NERAL n m b)
traverseNE f (Last  t)   = Last <$> Tree.traverse f t
traverseNE f (Cons0   r) = Cons0 <$> traverseNE f r
traverseNE f (Cons1 t r) = Cons1 <$> Tree.traverse f t <*> traverseNE f r

itraverse :: Applicative f => (Pos n -> a -> f b) -> RAL n a -> f (RAL n b)
itraverse _ Empty        = pure Empty
itraverse f (NonEmpty r) = NonEmpty <$> itraverseNE (f . Pos) r

itraverseNE :: Applicative f => (PosN n m -> a -> f b) -> NERAL n m a -> f (NERAL n m b)
itraverseNE f (Last  t)   = Last <$> Tree.itraverse (f . AtEnd) t
itraverseNE f (Cons0   r) = Cons0 <$> itraverseNE (f . There0) r
itraverseNE f (Cons1 t r) = Cons1 <$> Tree.itraverse (f . Here) t <*> itraverseNE (f . There1) r

traverse1 :: Apply f => (a -> f b) -> RAL ('BN n) a -> f (RAL ('BN n) b)
traverse1 f (NonEmpty r) = NonEmpty <$> traverse1NE f r

traverse1NE :: Apply f => (a -> f b) -> NERAL n m a -> f (NERAL n m b)
traverse1NE f (Last  t)   = Last <$> Tree.traverse1 f t
traverse1NE f (Cons0   r) = Cons0 <$> traverse1NE f r
traverse1NE f (Cons1 t r) = Cons1 <$> Tree.traverse1 f t <.> traverse1NE f r

itraverse1 :: Apply f => (Pos ('BN n) -> a -> f b) -> RAL ('BN n) a -> f (RAL ('BN n) b)
itraverse1 f (NonEmpty r) = NonEmpty <$> itraverse1NE (f . Pos) r

itraverse1NE :: Apply f => (PosN n m -> a -> f b) -> NERAL n m a -> f (NERAL n m b)
itraverse1NE f (Last  t)   = Last <$> Tree.itraverse1 (f . AtEnd) t
itraverse1NE f (Cons0   r) = Cons0 <$> itraverse1NE (f . There0) r
itraverse1NE f (Cons1 t r) = Cons1 <$> Tree.itraverse1 (f . Here) t <.> itraverse1NE (f . There1) r

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'RAL's with a function.
zipWith :: (a -> b -> c) -> RAL n a -> RAL n b -> RAL n c
zipWith _ Empty         Empty         = Empty
zipWith f (NonEmpty xs) (NonEmpty ys) = NonEmpty (zipWithNE f xs ys)

-- | Zip two 'NERAL's with a function.
zipWithNE :: (a -> b -> c) -> NERAL n m a -> NERAL n m b -> NERAL n m c
zipWithNE f (Last  t)   (Last  t')    = Last (Tree.zipWith f t t')
zipWithNE f (Cons0   r) (Cons0    r') = Cons0 (zipWithNE f r r')
zipWithNE f (Cons1 t r) (Cons1 t' r') = Cons1 (Tree.zipWith f t t') (zipWithNE f r r')

-- | Zip two 'RAL's with a function which also takes 'Pos' index.
izipWith :: (Pos n -> a -> b -> c) -> RAL n a -> RAL n b -> RAL n c
izipWith _ Empty         Empty         = Empty
izipWith f (NonEmpty xs) (NonEmpty ys) = NonEmpty (izipWithNE (f . Pos) xs ys)

-- | Zip two 'NERAL's with a function which also takes 'PosN' index.
izipWithNE :: (PosN n m -> a -> b -> c) -> NERAL n m a -> NERAL n m b -> NERAL n m c
izipWithNE f (Last  t)   (Last  t')    = Last (Tree.izipWith (f . AtEnd) t t')
izipWithNE f (Cons0   r) (Cons0    r') = Cons0 (izipWithNE (f . There0) r r')
izipWithNE f (Cons1 t r) (Cons1 t' r') = Cons1 (Tree.izipWith (f . Here) t t') (izipWithNE (f . There1) r r')

-- | Repeat a value.
--
-- >>> repeat 'x' :: RAL Bin5 Char
-- NonEmpty (Cons1 (Leaf 'x') (Cons0 (Last (Node (Node (Leaf 'x') (Leaf 'x')) (Node (Leaf 'x') (Leaf 'x'))))))
--
repeat :: forall b a. SBinI b => a -> RAL b a
repeat x = case sbin :: SBin b of
    SBZ -> Empty
    SBN -> NonEmpty (repeatNE x)

repeatNE :: forall b n a. (N.SNatI n, SBinNI b) => a -> NERAL n b a
repeatNE x = case sbinN :: SBinN b of
    SBE -> Last (Tree.repeat x)
    SB0 -> Cons0 (repeatNE x)
    SB1 -> Cons1 (Tree.repeat x) (repeatNE x)

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- |
--
-- >>> universe :: RAL Bin2 (Pos Bin2)
-- NonEmpty (Cons0 (Last (Node (Leaf 0) (Leaf 1))))
--
-- >>> let u = universe :: RAL Bin3 (Pos Bin3)
-- >>> u
-- NonEmpty (Cons1 (Leaf 0) (Last (Node (Leaf 1) (Leaf 2))))
--
-- >>> explicitShow $ u ! Pos (Here VNil)
-- "Pos (Here VNil)"
--
-- >>> let u' = universe :: RAL Bin5 (Pos Bin5)
--
-- >>> toList u' == sort (toList u')
-- True
--
universe :: forall b. SBinI b => RAL b (Pos b)
universe = case sbin :: SBin b of
    SBZ -> Empty
    SBN -> NonEmpty (fmap Pos universeNE)

universeNE :: forall n b. (N.SNatI n, SBinNI b) => NERAL n b (PosN n b)
universeNE = case sbinN :: SBinN b of
    SBE -> Last   (fmap AtEnd Tree.universe)
    SB0 -> Cons0 (fmap There0 universeNE)
    SB1 -> Cons1 (fmap Here Tree.universe) (fmap There1 universeNE)
