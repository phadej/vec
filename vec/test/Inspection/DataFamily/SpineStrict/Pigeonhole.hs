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
module Inspection.DataFamily.SpineStrict.Pigeonhole where

import Data.Vec.DataFamily.SpineStrict.Pigeonhole
       (gindex, gitraverse, gtabulate, gtraverse)
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

inspect $ 'lhsIndex === 'rhsIndex

-------------------------------------------------------------------------------
-- Tabulate
-------------------------------------------------------------------------------

lhsTabulate :: (Key -> a) -> Values a
lhsTabulate = gtabulate

rhsTabulate :: (Key -> a) -> Values a
rhsTabulate f = Values (f Key1) (f Key2) (f Key3) (f Key4) (f Key5)

inspect $ 'lhsTabulate === 'rhsTabulate

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

inspect $ 'lhsITraverse === 'rhsITraverse
