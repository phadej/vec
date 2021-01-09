{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
-- | Depth indexed perfect tree as data family.
module Data.RAVec.Tree.DF (
    Tree (..),

    -- * Construction
    singleton,

    -- * Conversions
    toList,
    reverse,

    -- * Indexing
    (!),
    tabulate,
    leftmost,
    rightmost,

    -- * Folds
    foldMap,
    foldMap1,
    ifoldMap,
    ifoldMap1,
    foldr,
    ifoldr,
    foldr1Map,
    ifoldr1Map,
    foldl,
    ifoldl,

    -- * Special folds
    length,
    null,
    sum,
    product,

    -- * Mapping
    map,
    imap,
    traverse,
    itraverse,
#ifdef MIN_VERSION_semigroupoids
    traverse1,
    itraverse1,
#endif
    itraverse_,

    -- * Zipping
    zipWith,
    izipWith,
    repeat,

    -- * Universe
    universe,

    -- * QuickCheck
    liftArbitrary,
    liftShrink,

    -- * Ensure spine
    ensureSpine,
) where

import Prelude
       (Bool (..), Eq (..), Functor (..), Int, Num, Ord (..), Ordering (..),
       Show (..), ShowS, flip, id, seq, showChar, showParen, showString,
       uncurry, ($), (&&), (*), (+), (.))

import Control.Applicative (Applicative (..), liftA2, (<$>))
import Control.DeepSeq     (NFData (..))
import Control.Monad       (void)
import Data.Hashable       (Hashable (..))
import Data.Monoid         (Monoid (..))
import Data.Nat            (Nat (..))
import Data.Semigroup      (Semigroup (..))
import Data.Wrd            (Wrd (..))

import qualified Data.Type.Nat as N

-- instances
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

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Proxy (Proxy (..))
-- >>> import Prelude (Char, not, uncurry, flip, error)

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data family Tree (n :: Nat) a

newtype instance Tree 'Z     a = Leaf a
data instance    Tree ('S n) a = Node (Tree n a) (Tree n a)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Eq a, N.SNatI n) => Eq (Tree n a) where
    (==) = getEqual (N.induction1 start step) where
        start :: Equal 'Z a
        start = Equal $ \(Leaf x) (Leaf y) -> x == y

        step :: Equal m a -> Equal ('S m) a
        step (Equal go) = Equal $ \(Node x1 y1) (Node x2 y2) ->
            go x1 x2 && go y1 y2

newtype Equal n a = Equal { getEqual :: Tree n a -> Tree n a -> Bool }

instance (Ord a, N.SNatI n) => Ord (Tree n a) where
    compare = getCompare (N.induction1 start step) where
        start :: Compare 'Z a
        start = Compare $ \(Leaf x) (Leaf y) -> compare x y

        step :: Compare m a -> Compare ('S m) a
        step (Compare go) = Compare $ \(Node x1 y1) (Node x2 y2) ->
            go x1 x2 <> go y1 y2

newtype Compare n a = Compare { getCompare :: Tree n a -> Tree n a -> Ordering }

instance (Show a, N.SNatI n) => Show (Tree n a) where
    showsPrec = getShowsPrec (N.induction1 start step) where
        start :: ShowsPrec 'Z a
        start = ShowsPrec $ \d (Leaf x) -> showParen (d > 10)
            $ showString "Leaf "
            . showsPrec 11 x

        step :: ShowsPrec m a -> ShowsPrec ('S m) a
        step (ShowsPrec go) = ShowsPrec $ \d (Node x y) -> showParen (d > 10)
            $ showString "Node "
            . go 11 x
            . showChar ' '
            . go 11 y

newtype ShowsPrec n a = ShowsPrec { getShowsPrec :: Int -> Tree n a -> ShowS }

instance N.SNatI n => Functor (Tree n) where
    fmap = map

instance N.SNatI n => I.Foldable (Tree n) where
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
instance (N.SNatI n) => I.Foldable1 (Tree n) where
    foldMap1 = foldMap1

instance (N.SNatI n) => I.Traversable1 (Tree n) where
    traverse1 = traverse1
#endif

instance N.SNatI n => I.Traversable (Tree n) where
    traverse = traverse

-- | @since 0.2
instance N.SNatI n => WI.FunctorWithIndex (Wrd n) (Tree n) where
    imap = imap

-- | @since 0.2
instance N.SNatI n => WI.FoldableWithIndex (Wrd n) (Tree n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

-- | @since 0.2
instance N.SNatI n => WI.TraversableWithIndex (Wrd n) (Tree n) where
    itraverse = itraverse

instance (NFData a, N.SNatI n) => NFData (Tree n a) where
    rnf = getRnf (N.induction1 z s) where
        z           = Rnf $ \(Leaf x)   -> rnf x
        s (Rnf rec) = Rnf $ \(Node x y) -> rec x `seq` rec y

newtype Rnf n a = Rnf { getRnf :: Tree n a -> () }

instance (Hashable a, N.SNatI n) => Hashable (Tree n a) where
    hashWithSalt = getHashWithSalt (N.induction1 z s) where
        z = HashWithSalt $ \salt (Leaf x) -> salt `hashWithSalt` x
        s (HashWithSalt rec) = HashWithSalt $ \salt (Node x y) -> rec (rec salt x) y

newtype HashWithSalt n a = HashWithSalt { getHashWithSalt :: Int -> Tree n a -> Int }

instance N.SNatI n => Applicative (Tree n) where
    pure = repeat
    (<*>)  = zipWith ($)
    _ *> x = x
    x <* _ = x
#if MIN_VERSION_base(4,10,0)
    liftA2 = zipWith
#endif

-- TODO: Monad

#ifdef MIN_VERSION_distributive
instance N.SNatI n => I.Distributive (Tree n) where
    distribute f = tabulate (\k -> fmap (! k) f)

#ifdef MIN_VERSION_adjunctions
instance N.SNatI n => I.Representable (Tree n) where
    type Rep (Tree n) = Wrd n
    tabulate = tabulate
    index    = (!)
#endif
#endif

instance (Semigroup a, N.SNatI n) => Semigroup (Tree n a) where
    (<>) = zipWith (<>)

instance (Monoid a, N.SNatI n) => Monoid (Tree n a) where
    mempty = pure mempty
    mappend = zipWith mappend

#ifdef MIN_VERSION_semigroupoids
instance N.SNatI n => Apply (Tree n) where
    (<.>) = zipWith ($)
    _ .> x = x
    x <. _ = x
    liftF2 = zipWith

-- TODO: Bind
#endif

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

-- | 'Tree' with exactly one element.
--
-- >>> singleton True
-- Leaf True
--
singleton :: a -> Tree 'Z a
singleton = Leaf

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert 'Tree' to list.
--
-- >>> toList $ Node (Node (Leaf 'f') (Leaf 'o')) (Node (Leaf 'o') (Leaf 'd'))
-- "food"
toList :: forall n a. N.SNatI n => Tree n a -> [a]
toList xs = getToList (N.induction1 start step) xs [] where
    start :: ToList 'Z a
    start = ToList (\(Leaf x) -> (x :))

    step :: ToList m a -> ToList ('S m) a
    step (ToList f) = ToList $ \(Node x y) -> f x . f y

newtype ToList n a = ToList { getToList :: Tree n a -> [a] -> [a] }

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

flipIndex :: N.SNatI n => Wrd n -> Tree n a -> a
flipIndex = getIndex (N.induction1 start step) where
    start :: Index 'Z a
    start = Index $ \_ (Leaf x) -> x

    step :: Index m a-> Index ('N.S m) a
    step (Index go) = Index $ \i (Node x y) -> case i of
        W0 j -> go j x
        W1 j -> go j y

newtype Index n a = Index { getIndex :: Wrd n -> Tree n a -> a }

-- | Indexing.
--
-- >>> let t = Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- >>> t ! W1 (W0 WE)
-- 'c'
--
(!) :: N.SNatI n => Tree n a -> Wrd n -> a
(!) = flip flipIndex

-- | Tabulating, inverse of '!'.
--
-- >>> tabulate id :: Tree N.Nat2 (Wrd N.Nat2)
-- Node (Node (Leaf 0b00) (Leaf 0b01)) (Node (Leaf 0b10) (Leaf 0b11))
tabulate :: N.SNatI n => (Wrd n -> a) -> Tree n a
tabulate = getTabulate (N.induction1 start step) where
    start :: Tabulate 'Z a
    start = Tabulate $ \f -> Leaf (f WE)

    step :: Tabulate m a -> Tabulate ('S m) a
    step (Tabulate go) = Tabulate $ \f -> Node (go (f . W0)) (go (f . W1))

newtype Tabulate n a = Tabulate { getTabulate :: (Wrd n -> a) -> Tree n a }

leftmost :: N.SNatI n => Tree n a -> a
leftmost = getTheMost (N.induction1 start step) where
    start :: TheMost 'Z a
    start = TheMost $ \(Leaf x) -> x

    step :: TheMost m a -> TheMost ('S m) a
    step (TheMost go) = TheMost $ \(Node x _) -> go x

rightmost :: N.SNatI n => Tree n a -> a
rightmost = getTheMost (N.induction1 start step) where
    start :: TheMost 'Z a
    start = TheMost $ \(Leaf x) -> x

    step :: TheMost m a -> TheMost ('S m) a
    step (TheMost go) = TheMost $ \(Node _ y) -> go y

newtype TheMost n a = TheMost { getTheMost :: Tree n a -> a }

-------------------------------------------------------------------------------
-- Reverse
-------------------------------------------------------------------------------

-- | Reverse 'Tree'.
--
-- >>> let t = Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- >>> reverse t
-- Node (Node (Leaf 'd') (Leaf 'c')) (Node (Leaf 'b') (Leaf 'a'))
--
reverse :: forall n a. N.SNatI n => Tree n a -> Tree n a
reverse = getReverse (N.induction1 start step) where
    start :: Reverse 'Z a
    start = Reverse id

    step :: N.SNatI m => Reverse m a -> Reverse ('S m) a
    step (Reverse go) = Reverse $ \(Node x y) -> Node (go y) (go x)

newtype Reverse n a = Reverse { getReverse :: Tree n a -> Tree n a }

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- | >>> map not $ Node (Leaf True) (Leaf False)
-- Node (Leaf False) (Leaf True)
--
map :: forall a b n. N.SNatI n => (a -> b) -> Tree n a -> Tree n b
map f = getMap $ N.induction1 start step where
    start :: Map a 'Z b
    start = Map $ \(Leaf x) -> Leaf (f x)

    step :: Map a m b -> Map a ('S m) b
    step (Map go) = Map $ \(Node x y) -> Node (go x) (go y)

newtype Map a n b = Map { getMap :: Tree n a -> Tree n b }

-- |
-- >>> let t = Node (Node (Leaf 'a') (Leaf 'b')) (Node (Leaf 'c') (Leaf 'd'))
-- >>> imap (,) t
-- Node (Node (Leaf (0b00,'a')) (Leaf (0b01,'b'))) (Node (Leaf (0b10,'c')) (Leaf (0b11,'d')))
--
imap :: N.SNatI n => (Wrd n -> a -> b) -> Tree n a -> Tree n b
imap = getIMap $ N.induction1 start step where
    start :: IMap a 'Z b
    start = IMap $ \f (Leaf x) -> Leaf (f WE x)

    step :: IMap a m b -> IMap a ('S m) b
    step (IMap go) = IMap $ \f (Node x y) ->
        Node (go (f . W0) x) (go (f . W1) y)

newtype IMap a n b = IMap { getIMap :: (Wrd n -> a -> b) -> Tree n a -> Tree n b }

-- | Apply an action to every element of a 'Tree', yielding a 'Tree' of results.
traverse :: forall n f a b. (Applicative f, N.SNatI n) => (a -> f b) -> Tree n a -> f (Tree n b)
traverse f =  getTraverse $ N.induction1 start step where
    start :: Traverse f a 'Z b
    start = Traverse $ \(Leaf x) -> Leaf <$> f x

    step :: Traverse f a m b -> Traverse f a ('S m) b
    step (Traverse go) = Traverse $ \(Node x y) -> liftA2 Node (go x) (go y)
{-# INLINE traverse #-}

newtype Traverse f a n b = Traverse { getTraverse :: Tree n a -> f (Tree n b) }

-- | Apply an action to every element of a 'Tree' and its index, yielding a 'Tree' of results.
itraverse :: forall n f a b. (Applicative f, N.SNatI n) => (Wrd n -> a -> f b) -> Tree n a -> f (Tree n b)
itraverse = getITraverse $ N.induction1 start step where
    start :: ITraverse f a 'Z b
    start = ITraverse $ \f (Leaf x) -> Leaf <$> f WE x

    step :: ITraverse f a m b -> ITraverse f a ('S m) b
    step (ITraverse go) = ITraverse $ \f (Node x y) -> liftA2 Node (go (f . W0) x) (go (f . W1) y)
{-# INLINE itraverse #-}

newtype ITraverse f a n b = ITraverse { getITraverse :: (Wrd n -> a -> f b) -> Tree n a -> f (Tree n b) }

#ifdef MIN_VERSION_semigroupoids
-- | Apply an action to non-empty 'Tree', yielding a 'Tree' of results.
traverse1 :: forall n f a b. (Apply f, N.SNatI n) => (a -> f b) -> Tree n a -> f (Tree n b)
traverse1 f = getTraverse $ N.induction1 start step where
    start :: Traverse f a 'Z b
    start = Traverse $ \(Leaf x) -> Leaf <$> f x

    step :: Traverse f a m b -> Traverse f a ('S m) b
    step (Traverse go) = Traverse $ \(Node x y) -> liftF2 Node (go x) (go y)
{-# INLINE traverse1 #-}

itraverse1 :: forall n f a b. (Apply f, N.SNatI n) => (Wrd n -> a -> f b) -> Tree n a -> f (Tree n b)
itraverse1 = getITraverse $ N.induction1 start step where
    start :: ITraverse f a 'Z b
    start = ITraverse $ \f (Leaf x) -> Leaf <$> f WE x

    step :: ITraverse f a m b -> ITraverse f a ('S m) b
    step (ITraverse go) = ITraverse $ \f (Node x y) -> liftF2 Node (go (f . W0) x) (go (f . W1) y)
{-# INLINE itraverse1 #-}
#endif

-- | Apply an action to every element of a 'Tree' and its index, ignoring the results.
itraverse_ :: forall n f a b. (Applicative f, N.SNatI n) => (Wrd n -> a -> f b) -> Tree n a -> f ()
itraverse_ = getITraverse_ $ N.induction1 start step where
    start :: ITraverse_ f a 'Z b
    start = ITraverse_ $ \f (Leaf x) -> void (f WE x)

    step :: ITraverse_ f a m b -> ITraverse_ f a ('S m) b
    step (ITraverse_ go) = ITraverse_ $ \f (Node x y) -> go (f . W0) x *> go (f . W1) y

newtype ITraverse_ f a n b = ITraverse_ { getITraverse_ :: (Wrd n -> a -> f b) -> Tree n a -> f () }

-------------------------------------------------------------------------------
-- Folding
-------------------------------------------------------------------------------

-- | See 'I.Foldable'.
foldMap :: forall a n m. (Monoid m, N.SNatI n) => (a -> m) -> Tree n a -> m
foldMap f = getFold (N.induction1 start step) where
    start :: Fold a 'Z m
    start = Fold $ \(Leaf x) -> f x

    step :: Fold a p m -> Fold a ('S p) m
    step (Fold g) = Fold $ \(Node x y) -> g x `mappend` g y

newtype Fold a n b = Fold  { getFold  :: Tree n a -> b }

-- | See 'I.Foldable1'.
foldMap1 :: forall s a n. (Semigroup s, N.SNatI n) => (a -> s) -> Tree n a -> s
foldMap1 f = getFold $ N.induction1 start step where
    start :: Fold a 'Z s
    start = Fold $ \(Leaf x) -> f x

    step :: Fold a m s -> Fold a ('S m) s
    step (Fold g) = Fold $ \(Node x y) -> g x <> g y

-- | See 'I.FoldableWithIndex'.
ifoldMap :: forall a n m. (Monoid m, N.SNatI n) => (Wrd n -> a -> m) -> Tree n a -> m
ifoldMap = getIFoldMap $ N.induction1 start step where
    start :: IFoldMap a 'Z m
    start = IFoldMap $ \f (Leaf x) -> f WE x

    step :: IFoldMap a p m -> IFoldMap a ('S p) m
    step (IFoldMap go) = IFoldMap $ \f (Node x y) -> go (f . W0) x `mappend` go (f . W1) y

newtype IFoldMap a n m = IFoldMap { getIFoldMap :: (Wrd n -> a -> m) -> Tree n a -> m }

-- | There is no type-class for this :(
ifoldMap1 :: forall a n s. (Semigroup s, N.SNatI n) => (Wrd ('S n) -> a -> s) -> Tree ('S n) a -> s
ifoldMap1 = getIFoldMap $ N.induction1 start step where
    start :: IFoldMap a 'Z m
    start = IFoldMap $ \f (Leaf x) -> f WE x

    step :: IFoldMap a p s -> IFoldMap a ('S p) s
    step (IFoldMap go) = IFoldMap $ \f (Node x y) -> go (f . W0) x <> go (f . W1) y




-- | Right fold.
foldr :: forall a b n. N.SNatI n => (a -> b -> b) -> b -> Tree n a -> b
foldr f = getFoldr (N.induction1 start step) where
    start :: Foldr a 'Z b
    start = Foldr $ \z (Leaf x) -> f x z

    step :: Foldr a m b -> Foldr a ('S m) b
    step (Foldr go) = Foldr $ \z (Node x y) -> go (go z y) x

newtype Foldr a n b = Foldr { getFoldr :: b -> Tree n a -> b }

-- | Right fold with an index.
ifoldr :: forall a b n. N.SNatI n => (Wrd n -> a -> b -> b) -> b -> Tree n a -> b
ifoldr = getIFoldr $ N.induction1 start step where
    start :: IFoldr a 'Z b
    start = IFoldr $ \f z (Leaf x) -> f WE x z

    step :: IFoldr a m b -> IFoldr a ('S m) b
    step (IFoldr go) = IFoldr $ \f z (Node x y) -> go (f . W0) (go (f . W1) z y) x

newtype IFoldr a n b = IFoldr { getIFoldr :: (Wrd n -> a -> b -> b) -> b -> Tree n a -> b }

foldr1Map :: forall a b n. N.SNatI n => (a -> b -> b) -> (a -> b) -> Tree n a -> b
foldr1Map f = getFoldr1 (N.induction1 start step) where
    start :: Foldr1 a 'Z b
    start = Foldr1 $ \z (Leaf x) -> z x

    step :: Foldr1 a m b -> Foldr1 a ('S m) b
    step (Foldr1 go) = Foldr1 $ \z (Node x y) -> go (\z0 -> f z0 (go z y)) x

newtype Foldr1 a n b = Foldr1 { getFoldr1 :: (a -> b) -> Tree n a -> b }

ifoldr1Map :: (Wrd n -> a -> b -> b) -> (Wrd n -> a -> b) -> Tree n a -> b
ifoldr1Map = ifoldr1Map

-- | Left fold.
foldl :: forall a b n. N.SNatI n => (b -> a -> b) -> b -> Tree n a -> b
foldl f = getFoldl (N.induction1 start step) where
    start :: Foldl a 'Z b
    start = Foldl $ \z (Leaf x) -> f z x

    step :: Foldl a m b -> Foldl a ('S m) b
    step (Foldl go) = Foldl $ \z (Node x y) -> go (go z x) y

newtype Foldl a n b = Foldl { getFoldl :: b -> Tree n a -> b }

-- | Left fold with an index.
ifoldl :: forall a b n. N.SNatI n => (Wrd n -> b -> a -> b) -> b -> Tree n a -> b
ifoldl = getIFoldl $ N.induction1 start step where
    start :: IFoldl a 'Z b
    start = IFoldl $ \f z (Leaf x) -> f WE z x

    step :: IFoldl a m b -> IFoldl a ('S m) b
    step (IFoldl go) = IFoldl $ \f z (Node x y) -> go (f . W0) (go (f . W1) z x) y

newtype IFoldl a n b = IFoldl { getIFoldl :: (Wrd n -> b -> a -> b) -> b -> Tree n a -> b }

-- | Yield the length of a 'Tree'. /O(n)/
length :: forall n a. N.SNatI n => Tree n a -> Int
length _ = getLength l where
    l :: Length n
    l = N.induction (Length 1) $ \(Length n) -> Length (2 * n)

newtype Length (n :: Nat) = Length { getLength :: Int }

-- | Test whether a 'Tree' is empty. It never is. /O(1)/
null :: Tree n a -> Bool
null _ = False

-------------------------------------------------------------------------------
-- Special folds
-------------------------------------------------------------------------------

-- | Non-strict 'sum'.
sum :: (Num a, N.SNatI n) => Tree n a -> a
sum = getFold $ N.induction1 start step where
    start :: Num a => Fold a 'Z a
    start = Fold $ \(Leaf x) -> x

    step :: Num a => Fold a m a -> Fold a ('S m) a
    step (Fold f) = Fold $ \(Node x y) -> f x + f y

-- | Non-strict 'product'.
product :: (Num a, N.SNatI n) => Tree n a -> a
product = getFold $ N.induction1 start step where
    start :: Num a => Fold a 'Z a
    start = Fold $ \(Leaf x) -> x

    step :: Num a => Fold a m a -> Fold a ('S m) a
    step (Fold f) = Fold $ \(Node x y) -> f x * f y

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

-- | Zip two 'Tree's with a function.
zipWith :: forall a b c n. N.SNatI n => (a -> b -> c) -> Tree n a -> Tree n b -> Tree n c
zipWith f = getZipWith $ N.induction start step where
    start :: ZipWith a b c 'Z
    start = ZipWith $ \(Leaf x) (Leaf y) -> Leaf (f x y)

    step :: ZipWith a b c m -> ZipWith a b c ('S m)
    step (ZipWith go) = ZipWith $ \(Node x y) (Node u v) -> Node (go x u) (go y v)

newtype ZipWith a b c n = ZipWith { getZipWith :: Tree n a -> Tree n b -> Tree n c }

-- | Zip two 'Tree's. with a function that also takes the elements' indices.
izipWith :: N.SNatI n => (Wrd n -> a -> b -> c) -> Tree n a -> Tree n b -> Tree n c
izipWith = getIZipWith $ N.induction start step where
    start :: IZipWith a b c 'Z
    start = IZipWith $ \f (Leaf x) (Leaf y) -> Leaf (f WE x y)

    step :: IZipWith a b c m -> IZipWith a b c ('S m)
    step (IZipWith go) = IZipWith $ \f (Node x y) (Node u v) -> Node (go (f . W0) x u) (go (f . W1) y v)

newtype IZipWith a b c n = IZipWith { getIZipWith :: (Wrd n -> a -> b -> c) -> Tree n a -> Tree n b -> Tree n c }

-- | Repeat value
--
-- >>> repeat 'x' :: Tree N.Nat2 Char
-- Node (Node (Leaf 'x') (Leaf 'x')) (Node (Leaf 'x') (Leaf 'x'))
--
repeat :: N.SNatI n => x -> Tree n x
repeat x = N.induction1 (Leaf x) $ \t -> Node t t

-------------------------------------------------------------------------------
-- Monadic
-------------------------------------------------------------------------------

-- TODO

-------------------------------------------------------------------------------
-- universe
-------------------------------------------------------------------------------

-- | Get all @'Wrd' n@ in a @'Tree' n@.
--
-- >>> universe :: Tree N.Nat2 (Wrd N.Nat2)
-- Node (Node (Leaf 0b00) (Leaf 0b01)) (Node (Leaf 0b10) (Leaf 0b11))
universe :: N.SNatI n => Tree n (Wrd n)
universe = tabulate id

-------------------------------------------------------------------------------
-- EnsureSpine
-------------------------------------------------------------------------------

-- | Ensure spine.
--
-- If we have an undefined 'Tree',
--
-- >>> let v = error "err" :: Tree N.Nat2 Char
--
-- And insert data into it later:
--
-- >>> let setHead :: a -> Tree N.Nat2 a -> Tree N.Nat2 a; setHead x (Node (Node _ u) v) = Node (Node (Leaf x) u) v
--
-- Then without a spine, it will fail:
--
-- >>> leftmost $ setHead 'x' v
-- *** Exception: err
-- ...
--
-- But with the spine, it won't:
--
-- >>> leftmost $ setHead 'x' $ ensureSpine v
-- 'x'
--
ensureSpine :: N.SNatI n => Tree n a -> Tree n a
ensureSpine = getEnsureSpine (N.induction1 first step) where
    first :: EnsureSpine 'Z a
    first = EnsureSpine $ \ ~(Leaf x) -> Leaf x

    step :: EnsureSpine m a -> EnsureSpine ('S m) a
    step (EnsureSpine go) = EnsureSpine $ \ ~(Node x y) -> Node (go x) (go y)

newtype EnsureSpine n a = EnsureSpine { getEnsureSpine :: Tree n a -> Tree n a }

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance N.SNatI n => QC.Arbitrary1 (Tree n) where
    liftArbitrary = liftArbitrary
    liftShrink    = liftShrink

liftArbitrary :: forall n a. N.SNatI n => QC.Gen a -> QC.Gen (Tree n a)
liftArbitrary arb = getArb $ N.induction1 start step where
    start :: Arb 'Z a
    start = Arb $ Leaf <$> arb

    step :: Arb m a -> Arb ('S m) a
    step (Arb rec) = Arb $ liftA2 Node rec rec

newtype Arb n a = Arb { getArb :: QC.Gen (Tree n a) }

liftShrink :: forall n a. N.SNatI n => (a -> [a]) -> Tree n a -> [Tree n a]
liftShrink shr = getShr $ N.induction1 start step where
    start :: Shr 'Z a
    start = Shr $ \(Leaf x) ->Leaf <$> shr x

    step :: Shr m a -> Shr ('S m) a
    step (Shr rec) = Shr $ \(Node x y) ->
        uncurry Node <$> QC.liftShrink2 rec rec (x, y)

newtype Shr n a = Shr { getShr :: Tree n a -> [Tree n a] }

instance (N.SNatI n, QC.Arbitrary a) => QC.Arbitrary (Tree n a) where
    arbitrary = QC.arbitrary1
    shrink    = QC.shrink1

instance (N.SNatI n, QC.CoArbitrary a) => QC.CoArbitrary (Tree n a) where
    coarbitrary v = case N.snat :: N.SNat n of
        N.SZ -> QC.variant (0 :: Int) . (case v of (Leaf x) -> QC.coarbitrary x)
        N.SS -> QC.variant (1 :: Int) . (case v of (Node x y) -> QC.coarbitrary (x, y))

instance (N.SNatI n, QC.Function a) => QC.Function (Tree n a) where
    function = case N.snat :: N.SNat n of
        N.SZ -> QC.functionMap (\(Leaf x) -> x) Leaf
        N.SS -> QC.functionMap (\(Node x y) -> (x, y)) (\(x,y) -> Node x y)
