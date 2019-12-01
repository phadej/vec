{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

-- This need is quite subtle
{-# LANGUAGE AllowAmbiguousTypes #-}
module ModelTest (
    modelTest,
    -- * Lifters
    mapUA,
    mapAA,
    mapAX,
    mapXA,
    mapAAX,
    mapAAA,
    mapAXA,
    mapAXY,
    ) where

import Data.Proxy            (Proxy (..))
import Test.Tasty            (TestName, TestTree)
import Test.Tasty.QuickCheck (testProperty)

import Control.Applicative (liftA2)
import Data.Coerce         (coerce)

import qualified Test.QuickCheck as QC

-------------------------------------------------------------------------------
-- Generic model test
-------------------------------------------------------------------------------

-- | Model test, given
--
-- @
-- a2b ::                    a -> b
-- f2g :: forall x. c x -> f x -> g x
-- @
--
-- We can test whether a square commutes:
--
-- @
--                 f2g
--         f a ------------> g a
--          |                 |
-- fmap a2b |       = ?       | fmap a2b
--          V                 V
--         f b ------------> g b
--                 f2g
-- @
--
-- By using different @f@ and @g@ 'Functor's, like @Identity@, @K@,
-- @(x,-)@ and their combinations, we can test unary, binary,
-- parametrised etc. functions.
--
-- 'mapAA', 'mapAX'... etc functions use own 'Functor's, which
-- 'Show' instance doesn't show newtype wrappers.
--
modelTest
    :: forall a b f g c.
    ( c a, c b
    , QC.Arbitrary (f a), Eq (g b)
    , Show (f a), Show (f b), Show (g a), Show (g b)
    , Functor f, Functor g
    )
    => (a -> b)
    -> Proxy c
    -> TestName
    -> (forall x. c x => f x -> g x)
    -> TestTree
modelTest a2b _ name f2g = testProperty name $ \fa ->
    let ga :: g a
        ga = f2g fa

        fb :: f b
        fb = fmap a2b fa

        gb :: g b
        gb = f2g fb

        gb' :: g b
        gb' = fmap a2b ga

        msg = unlines
            [ show fa                   ++ " --> " ++ show ga ++ " --> " ++ show gb
            , map (const ' ') (show fa) ++ " --> " ++ show fb ++ " --> " ++ show gb'
            ]

    in QC.counterexample msg $ gb' QC.=== gb

-------------------------------------------------------------------------------
-- Functor utilities
-------------------------------------------------------------------------------

mapUA :: a -> K () a -> I a
mapUA x _ = I x

mapAA :: (a -> a) -> I a -> I a
mapAA = coerce

mapXA :: (x -> a) -> K x a -> I a
mapXA = coerce

mapAX :: (a -> x) -> I a -> K x a
mapAX = coerce

mapAAX :: (a -> a -> x) -> V2 a -> K x a
mapAAX f (I x :*: I y) = K (f x y)

mapAAA :: (a -> a -> a) -> V2 a -> I a
mapAAA f (I x :*: I y) = I (f x y)

mapAXA :: (a -> x -> a) -> W x a -> I a
mapAXA f (K x :*: I a) = I (f a x)

mapAXY :: (a -> x -> y) -> W x a -> K y a
mapAXY f (K x :*: I a) = K (f a x)

-------------------------------------------------------------------------------
-- Identity
-------------------------------------------------------------------------------

newtype I a = I a deriving (Eq, Functor)

instance Show a => Show (I a) where
    showsPrec d (I a) = showsPrec d a

instance QC.Arbitrary a => QC.Arbitrary (I a) where
    arbitrary    = fmap I QC.arbitrary
    shrink (I a) = fmap I (QC.shrink a)

-------------------------------------------------------------------------------
-- Const
-------------------------------------------------------------------------------

newtype K b a = K b deriving (Eq, Functor)

instance Show b => Show (K b a) where
    showsPrec d (K b) = showsPrec d b

instance QC.Arbitrary b => QC.Arbitrary (K b a) where
    arbitrary    = fmap K QC.arbitrary
    shrink (K b) = fmap K (QC.shrink b)

-------------------------------------------------------------------------------
-- Product
-------------------------------------------------------------------------------

type V2  = I :*: I
type W b = K b :*: I

data (:*:) f g a = f a :*: g a deriving (Eq, Functor)
infixr 5 :*:

instance (Show (f a), Show (g a)) => Show ((:*:) f g a) where
    showsPrec d (a :*: b)
        = showParen (d > 5)
        $ showsPrec 6 a
        . showString " :*: "
        . showsPrec 5 b

instance (QC.Arbitrary (f a), QC.Arbitrary (g a)) => QC.Arbitrary ((:*:) f g a) where
    arbitrary        = liftA2 (:*:) QC.arbitrary QC.arbitrary
    shrink (a :*: b) = fmap (uncurry (:*:)) (QC.shrink (a, b))
