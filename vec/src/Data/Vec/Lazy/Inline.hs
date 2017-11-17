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
-- | TBW, inline
module Data.Vec.Lazy.Inline (
    Vec (..),
    -- * Conversions
    toPull,
    fromPull,
    toList, 
    -- toList
    -- * Indexing
    (!),
    head,
    -- * Sub-vectors
    tail,
    -- * Element-wise operations
    zipWith,
    sum,
    -- * VecEach
    VecEach (..),
    )  where

import Prelude ()
import Prelude.Compat hiding (head, tail, zipWith, sum)

import Data.Fin          (Fin)
import Data.Nat
import Data.Vec.Lazy     (Vec (..), head, tail, VecEach (..))

import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toPull :: forall n a. N.InlineInduction n => Vec n a -> P.Vec n a
toPull = getToPull (N.inlineInduction1 start step) where
    start :: ToPull 'Z a
    start = ToPull $ \_ -> P.Vec F.absurd

    step :: ToPull m a -> ToPull ('S m) a
    step (ToPull f) = ToPull $ \(x ::: xs) -> P.Vec $ \i -> case i of
        F.Z    -> x
        F.S i' -> P.unVec (f xs) i'

newtype ToPull n a = ToPull { getToPull :: Vec n a -> P.Vec n a }

fromPull :: forall n a. N.InlineInduction n => P.Vec n a -> Vec n a
fromPull = getFromPull (N.inlineInduction1 start step) where
    start :: FromPull 'Z a
    start = FromPull $ const VNil

    step :: FromPull m a -> FromPull ('S m) a
    step (FromPull f) = FromPull $ \(P.Vec v) -> v F.Z ::: f (P.Vec (v . F.S))

newtype FromPull n a = FromPull { getFromPull :: P.Vec n a -> Vec n a }

toList :: forall n a. N.InlineInduction n => Vec n a -> [a]
toList = getToList (N.inlineInduction1 start step) where
    start :: ToList 'Z a
    start = ToList (const [])

    step :: ToList m a -> ToList ('S m) a
    step (ToList f) = ToList $ \(x ::: xs) -> x : f xs

newtype ToList n a = ToList { getToList :: Vec n a -> [a] }

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Indexing
(!) :: N.InlineInduction n => Vec n a -> Fin n -> a
(!) = appIndex (N.inlineInduction1 start step) where
    start :: Index 'Z a
    start = Index $ \_ -> F.absurd

    step :: Index n a -> Index ('S n) a
    step (Index f) = Index $ \xs i -> case xs of 
        x ::: xs' -> case i of
            F.Z    -> x
            F.S i' -> f xs' i'

newtype Index n a = Index { appIndex :: Vec n a -> Fin n -> a }

-------------------------------------------------------------------------------
-- Concatenation
-------------------------------------------------------------------------------

-- (++)

-- split

-- concatMap
--
-- concat

-------------------------------------------------------------------------------
-- Mapping
-------------------------------------------------------------------------------

-- mapWithKey

traverseVec :: forall n f a b. Applicative f => (a -> f b) -> Vec n a -> f (Vec n b)
traverseVec f = go where
    go :: Vec m a -> f (Vec m b)
    go VNil       = pure VNil
    go (x ::: xs) = (:::) <$> f x <*> go xs

-- traverseWithKey

-- traverseWithKey_ 

-------------------------------------------------------------------------------
-- Folding
-------------------------------------------------------------------------------

-- foldr 
--
-- foldl'
--
-- foldrWithKey
--
-- foldlWithKey'

-- length

-- null

-- toList

sum :: forall a n. (N.InlineInduction n, Num a) => Vec n a -> a
sum = getSum $ N.inlineInduction1 start step where
    start :: Sum 'Z a
    start = Sum $ \VNil -> 0

    step :: Sum m a -> Sum ('S m) a
    step (Sum f) = Sum $ \(x ::: xs) -> x + f xs

newtype Sum n a = Sum { getSum :: Vec n a -> a }

-------------------------------------------------------------------------------
-- Element-wise operations
-------------------------------------------------------------------------------

zipWith :: forall a b c n. N.InlineInduction n => (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f = getZipWith $ N.inlineInduction start step where
    start :: ZipWith a b c 'Z
    start = ZipWith $ \_ _ -> VNil

    step :: ZipWith a b c m -> ZipWith a b c ('S m)
    step (ZipWith g) = ZipWith $ \(x ::: xs) (y ::: ys) -> f x y ::: g xs ys

newtype ZipWith a b c n = ZipWith { getZipWith :: Vec n a -> Vec n b -> Vec n c }

-- inlineZipWithKey
