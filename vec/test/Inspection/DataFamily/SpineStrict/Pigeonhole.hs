{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
-- {-# OPTIONS_GHC -dsuppress-all #-}
{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-coercions #-}
{-# OPTIONS_GHC -dsuppress-type-applications #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}
{-# OPTIONS_GHC -dsuppress-type-signatures #-}
-- {-# OPTIONS_GHC -dsuppress-uniques #-}
-- This makes gix tests pass, default is 60
{-# OPTIONS_GHC -funfolding-use-threshold=500 #-}
{-# OPTIONS_GHC -funfolding-keeness-factor=5 #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=2000 #-}
module Inspection.DataFamily.SpineStrict.Pigeonhole where

import Data.Functor.Compat                        ((<&>))
import Data.Vec.DataFamily.SpineStrict.Pigeonhole
       (gindex, gitraverse, gix, gtabulate, gtraverse)
import GHC.Generics                               (Generic, Generic1)
import Test.Inspection

-------------------------------------------------------------------------------
-- Simple type
-------------------------------------------------------------------------------

data Key = K1 | K2 | K3 | K4 | K5 | K6 | K7 | K8 | K9 deriving (Show, Generic)
data Values a = Values a a a a a a a a a deriving (Show, Generic1)

-------------------------------------------------------------------------------
-- Simple
-------------------------------------------------------------------------------

lhsSimple :: Char
lhsSimple = gindex (Values 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i') K2

rhsSimple :: Char
rhsSimple = 'b'

inspect $ 'lhsSimple === 'rhsSimple

-------------------------------------------------------------------------------
-- Index
-------------------------------------------------------------------------------

lhsIndex :: Values a -> Key -> a
lhsIndex = gindex

rhsIndex :: Values a -> Key -> a
rhsIndex (Values x _ _ _ _ _ _ _ _) K1 = x
rhsIndex (Values _ x _ _ _ _ _ _ _) K2 = x
rhsIndex (Values _ _ x _ _ _ _ _ _) K3 = x
rhsIndex (Values _ _ _ x _ _ _ _ _) K4 = x
rhsIndex (Values _ _ _ _ x _ _ _ _) K5 = x
rhsIndex (Values _ _ _ _ _ x _ _ _) K6 = x
rhsIndex (Values _ _ _ _ _ _ x _ _) K7 = x
rhsIndex (Values _ _ _ _ _ _ _ x _) K8 = x
rhsIndex (Values _ _ _ _ _ _ _ _ x) K9 = x

inspect $ hasNoGenerics 'lhsIndex
inspect $ 'lhsIndex === 'rhsIndex

-------------------------------------------------------------------------------
-- Tabulate
-------------------------------------------------------------------------------

lhsTabulate :: (Key -> a) -> Values a
lhsTabulate = gtabulate

rhsTabulate :: (Key -> a) -> Values a
rhsTabulate f = Values
    (f K1) (f K2) (f K3)
    (f K4) (f K5) (f K6)
    (f K7) (f K8) (f K9)

inspect $ hasNoGenerics 'lhsTabulate
inspect $ 'lhsTabulate === 'rhsTabulate

-------------------------------------------------------------------------------
-- Ix
-------------------------------------------------------------------------------

type LensLike' f s a = (a -> f a) -> s -> f s

lhsIx :: Functor f => Key -> LensLike' f (Values a) a
lhsIx = gix

rhsIx :: Functor f => Key -> LensLike' f (Values a) a
rhsIx K1 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x1 <&> \y1 -> Values y1 x2 x3 x4 x5 x6 x7 x8 x9
rhsIx K2 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x2 <&> \y2 -> Values x1 y2 x3 x4 x5 x6 x7 x8 x9
rhsIx K3 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x3 <&> \y3 -> Values x1 x2 y3 x4 x5 x6 x7 x8 x9
rhsIx K4 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x4 <&> \y4 -> Values x1 x2 x3 y4 x5 x6 x7 x8 x9
rhsIx K5 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x5 <&> \y5 -> Values x1 x2 x3 x4 y5 x6 x7 x8 x9
rhsIx K6 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x6 <&> \y6 -> Values x1 x2 x3 x4 x5 y6 x7 x8 x9
rhsIx K7 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x7 <&> \y7 -> Values x1 x2 x3 x4 x5 x6 y7 x8 x9
rhsIx K8 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x8 <&> \y8 -> Values x1 x2 x3 x4 x5 x6 x7 y8 x9
rhsIx K9 f (Values x1 x2 x3 x4 x5 x6 x7 x8 x9) = f x9 <&> \y9 -> Values x1 x2 x3 x4 x5 x6 x7 x8 y9

inspect $ hasNoGenerics 'lhsIx
inspect $ 'lhsIx === 'rhsIx

-------------------------------------------------------------------------------
-- Indexed traverse
-------------------------------------------------------------------------------

lhsTraverse :: Applicative f => (a -> f b) -> Values a -> f (Values b)
lhsTraverse f xs = gtraverse f xs

rhsTraverse :: Applicative f => (a -> f b) -> Values a -> f (Values b)
rhsTraverse f (Values x y z u v a b c d) = pure Values
    <*> f x
    <*> f y
    <*> f z
    <*> f u
    <*> f v
    <*> f a
    <*> f b
    <*> f c
    <*> f d

inspect $ hasNoGenerics 'lhsTraverse
inspect $ 'lhsTraverse === 'rhsTraverse

lhsITraverse :: Applicative f => (Key -> a -> f b) -> Values a -> f (Values b)
lhsITraverse f xs = gitraverse f xs

rhsITraverse :: Applicative f => (Key -> a -> f b) -> Values a -> f (Values b)
rhsITraverse f (Values x y z u v a b c d) = pure Values
    <*> f K1 x
    <*> f K2 y
    <*> f K3 z
    <*> f K4 u
    <*> f K5 v
    <*> f K6 a
    <*> f K7 b
    <*> f K8 c
    <*> f K9 d

inspect $ hasNoGenerics 'lhsITraverse
inspect $ 'lhsITraverse === 'rhsITraverse
