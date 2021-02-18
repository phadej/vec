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
{-# OPTIONS_GHC -funfolding-use-threshold=240 #-}
module Inspection.DataFamily.SpineStrict.Pigeonhole where

import Data.Functor.Compat                        ((<&>))
import Data.Vec.DataFamily.SpineStrict.Pigeonhole
       (gindex, gitraverse, gix, gtabulate, gtraverse)
import GHC.Generics                               (Generic, Generic1)
import Test.Inspection

-------------------------------------------------------------------------------
-- Simple type
-------------------------------------------------------------------------------

data Key = Key1 | Key2 | Key3 | Key4 | Key5 deriving (Show, Generic)
data Values a = Values a a a a a deriving (Show, Generic1)

-------------------------------------------------------------------------------
-- Simple
-------------------------------------------------------------------------------

lhsSimple :: Char
lhsSimple = gindex (Values 'a' 'b' 'c' 'd' 'e' ) Key2

rhsSimple :: Char
rhsSimple = 'b'

inspect $ 'lhsSimple === 'rhsSimple

-------------------------------------------------------------------------------
-- Index
-------------------------------------------------------------------------------

lhsIndex :: Values a -> Key -> a
lhsIndex = gindex

rhsIndex :: Values a -> Key -> a
rhsIndex (Values x _ _ _ _) Key1 = x
rhsIndex (Values _ x _ _ _) Key2 = x
rhsIndex (Values _ _ x _ _) Key3 = x
rhsIndex (Values _ _ _ x _) Key4 = x
rhsIndex (Values _ _ _ _ x) Key5 = x

inspect $ hasNoGenerics 'lhsIndex
inspect $ 'lhsIndex === 'rhsIndex

-------------------------------------------------------------------------------
-- Tabulate
-------------------------------------------------------------------------------

lhsTabulate :: (Key -> a) -> Values a
lhsTabulate = gtabulate

rhsTabulate :: (Key -> a) -> Values a
rhsTabulate f = Values (f Key1) (f Key2) (f Key3) (f Key4) (f Key5)

inspect $ hasNoGenerics 'lhsTabulate
inspect $ 'lhsTabulate === 'rhsTabulate

-------------------------------------------------------------------------------
-- Ix
-------------------------------------------------------------------------------

type LensLike' f s a = (a -> f a) -> s -> f s

lhsIx :: Functor f => Key -> LensLike' f (Values a) a
lhsIx = gix

rhsIx :: Functor f => Key -> LensLike' f (Values a) a
rhsIx Key1 f (Values x1 x2 x3 x4 x5) = f x1 <&> \x1' -> Values x1' x2 x3 x4 x5
rhsIx Key2 f (Values x1 x2 x3 x4 x5) = f x2 <&> \x2' -> Values x1 x2' x3 x4 x5
rhsIx Key3 f (Values x1 x2 x3 x4 x5) = f x3 <&> \x3' -> Values x1 x2 x3' x4 x5
rhsIx Key4 f (Values x1 x2 x3 x4 x5) = f x4 <&> \x4' -> Values x1 x2 x3 x4' x5
rhsIx Key5 f (Values x1 x2 x3 x4 x5) = f x5 <&> \x5' -> Values x1 x2 x3 x4 x5'

inspect $ hasNoGenerics 'lhsIx
inspect $ 'lhsIx === 'rhsIx

-------------------------------------------------------------------------------
-- Indexed traverse
-------------------------------------------------------------------------------

lhsTraverse :: Applicative f => (a -> f b) -> Values a -> f (Values b)
lhsTraverse f xs = gtraverse f xs

rhsTraverse :: Applicative f => (a -> f b) -> Values a -> f (Values b)
rhsTraverse f (Values x y z u v) = pure Values
    <*> f x
    <*> f y
    <*> f z
    <*> f u
    <*> f v

inspect $ hasNoGenerics 'lhsTraverse
inspect $ 'lhsTraverse === 'rhsTraverse

lhsITraverse :: Applicative f => (Key -> a -> f b) -> Values a -> f (Values b)
lhsITraverse f xs = gitraverse f xs

rhsITraverse :: Applicative f => (Key -> a -> f b) -> Values a -> f (Values b)
rhsITraverse f (Values x y z u v) = pure Values
    <*> f Key1 x
    <*> f Key2 y
    <*> f Key3 z
    <*> f Key4 u
    <*> f Key5 v

inspect $ hasNoGenerics 'lhsITraverse
inspect $ 'lhsITraverse === 'rhsITraverse
