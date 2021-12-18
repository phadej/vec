{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Test.QuickCheck       (label, counterexample, Arbitrary, Property, property, (===))
import Test.Tasty            (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)

import Data.Nat (Nat)

main :: IO ()
main = defaultMain $ testGroup "fin"
    [ ordLaws (0 :: Nat)
    ]

ordLaws :: forall a. (Arbitrary a, Ord a, Show a) => a -> TestTree
ordLaws p = testGroup "Ord"
    [ testProperty "comparability" prop_comp
    , testProperty "transivitity" prop_trans
    , testProperty "reflexivity" prop_refl
    , testProperty "asymmetry" prop_asym
    , testProperty "x >= y = y <= x" prop_def_ge
    , testProperty "x > y = y < x" prop_def_gt
    , testProperty "x <= y = compare x y /= GT" prop_le_comp
    , testProperty "x => y = compare x y /= LT" prop_ge_comp
    , testProperty "x < y = compare x y == LT" prop_lt_comp
    , testProperty "x > y = compare x y == GT" prop_gt_comp
    , testProperty "x == y = compare x y == EQ" prop_eq_comp
    , testProperty "min x y == if x <= y then x else y = True" prop_def_min
    , testProperty "max x y == if x >= y then x else y = True" prop_def_max
    , eqLaws p
    ]
  where
    prop_refl :: a -> Property
    prop_refl x = property (x <= x)

    prop_comp :: a -> a -> Property
    prop_comp x y = property (x <= y || y <= x)
    
    prop_trans :: a -> a -> a -> Property
    prop_trans x y z = counterexample (show (xy, yz, xz)) $
        case (xy, yz) of
            (True, True) -> label "True" xz
            _            -> label "False" True
      where
        xy = x <= y
        yz = y <= z
        xz = x <= z

    prop_asym :: a -> a -> Property
    prop_asym x y = counterexample (show (xy, yx, eq)) $
        case (xy, yx) of
            (True, True) -> label "True" eq
            _            -> label "False" True
      where
        xy = x <= y
        yx = y <= x
        eq = x == y

    prop_def_ge :: a -> a -> Property
    prop_def_ge x y = (x >= y) === (y <= x)

    prop_def_gt :: a -> a -> Property
    prop_def_gt x y = (x > y) === (y < x)

    prop_le_comp :: a -> a -> Property
    prop_le_comp x y = (x <= y) === (compare x y /= GT)

    prop_ge_comp :: a -> a -> Property
    prop_ge_comp x y = (x >= y) === (compare x y /= LT)

    prop_lt_comp :: a -> a -> Property
    prop_lt_comp x y = (x < y) === (compare x y == LT)

    prop_gt_comp :: a -> a -> Property
    prop_gt_comp x y = (x > y) === (compare x y == GT)

    prop_eq_comp :: a -> a -> Property
    prop_eq_comp x y = (x == y) === (compare x y == EQ)

    prop_def_min :: a -> a -> Property
    prop_def_min x y = min x y === (if x <= y then x else y)

    prop_def_max :: a -> a -> Property
    prop_def_max x y = max x y === (if x >= y then x else y)

eqLaws :: forall a. (Arbitrary a, Eq a, Show a) => a -> TestTree
eqLaws _ = testGroup "Ord"
    [ testProperty "reflexivity" prop_refl
    , testProperty "commutativity" prop_comm
    , testProperty "transitivity" prop_trans
    , testProperty "negation (default /=)" prop_neg
    -- cannot test substantivity
    ]
  where
    prop_refl :: a -> Property
    prop_refl x = x === x

    prop_comm :: a -> a -> Property
    prop_comm x y = (x == y) === (y == x)

    prop_trans :: a -> a -> a -> Property
    prop_trans x y z = counterexample (show (xy, yz, xz)) $
        -- here, only 0, 1, 3 can be True, i.e. only 2 cannot be True.
        -- we rely on commutatity to deduce this
        case sum (map fromEnum [xy, yz, xz]) of
            2 -> property False
            n -> label (show n) $ property True
      where
        xy = x == y
        yz = y == z
        xz = x == z

    prop_neg :: a -> a -> Property
    prop_neg x y = (x /= y) === (not (x == y))
