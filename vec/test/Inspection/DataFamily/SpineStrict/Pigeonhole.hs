{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
{-# OPTIONS_GHC -dsuppress-all #-}
module Inspection.DataFamily.SpineStrict.Pigeonhole where

import Data.Vec.DataFamily.SpineStrict.Pigeonhole (gindex, gtabulate)
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
