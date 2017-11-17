{-# LANGUAGE TypeFamilies #-}
module Data.Vec.Pull (
    Vec (..),
    -- * Operations
    (!),
    zipWith,
    zipWithKey,
    sum,
    ) where

import Prelude ()
import Prelude.Compat hiding (sum, zipWith)

import Data.Distributive (Distributive (..))
import Data.Fin          (Fin)
import Data.Functor.Rep  (Representable (..))
import Data.List         (foldl')
import Data.Semigroup    (Semigroup (..))

import qualified Data.Fin      as F
import qualified Data.Type.Nat as N

-- | Easily fuseable 'Vec'.
--
-- It unpurpose don't have /bad/ (fusion-wise) instances, like 'Traversable'.
-- Generally, there aren't functions which would be __bad consumers__ or __bad producers__.
newtype Vec n a = Vec { unVec :: Fin n -> a }

instance Functor (Vec n) where
    fmap f (Vec v) = Vec (f . v)

instance N.SNatI n => Foldable (Vec n) where
    foldMap f (Vec n) = foldMap (f . n) F.universe

instance Applicative (Vec n) where
    pure = Vec . pure
    (<*>) = zipWith ($)

instance Monad (Vec n) where
    return = pure
    m >>= k = Vec $ unVec m >>= unVec . k

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

-------------------------------------------------------------------------------
-- Operations
-------------------------------------------------------------------------------
-- | Indexing.
(!) :: Vec n a -> Fin n -> a
(!) = unVec

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f (Vec xs) (Vec ys) = Vec $ \i -> f (xs i) (ys i)

zipWithKey :: (Fin n -> a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithKey f (Vec xs) (Vec ys) = Vec $ \i -> f i (xs i) (ys i)

sum :: (N.SNatI n, Num a) => Vec n a -> a
sum (Vec f) = foldl' (\x i -> x + f i) 0 F.universe
