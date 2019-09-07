{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}
module Data.Type.Dec (
    -- * Types
    Neg,
    Dec (..),
    Decidable (..),
    DecideEq (..),
    -- * Neg combinators
    toNegNeg,
    tripleNeg,
    contradict,
    contraposition,
    -- * Dec combinators
    decNeg,
    decShow,
    decToMaybe,
    decToBool,
    ) where

import Data.Type.Equality ((:~:) (..))
import Data.Void          (Void)

-- | Intuitionistic negation.
type Neg a = a -> Void

-- | Decidable (nullary) relations.
data Dec a
    = Yes a
    | No (Neg a)

-- | Class of decidable types.
--
-- == Law
--
-- @a@ should be a Proposition, i.e. the 'Yes' answers should be unique.
--
-- /Note:/ We'd want to have decidable equality @:~:@ here too,
-- but that seems to be a deep dive into singletons.
class Decidable a where
    decide :: Dec a

-- | Decidable equality.
--
-- @since 0.0.4
class DecideEq s where
    decideEq :: s a -> s b -> Dec (a :~: b)

instance DecideEq ((:~:) c) where
    decideEq Refl Refl = Yes Refl

-------------------------------------------------------------------------------
-- Neg combinators
-------------------------------------------------------------------------------

-- | We can negate anything twice.
--
-- Double-negation elimination is inverse of 'toNegNeg' and generally
-- impossible.
toNegNeg :: a -> Neg (Neg a)
toNegNeg x = ($ x)

-- | Triple negation can be reduced to a single one.
tripleNeg :: Neg (Neg (Neg a)) -> Neg a
tripleNeg f a = f (toNegNeg a)

-- | Weak contradiction.
contradict :: (a -> Neg b) -> b -> Neg a
contradict f b a = f a b

-- | A variant of contraposition.
contraposition :: (a -> b) -> Neg b -> Neg a
contraposition f nb a = nb (f a)

-------------------------------------------------------------------------------
-- Dec combinators
-------------------------------------------------------------------------------

instance Eq a => Eq (Dec a) where
    Yes x == Yes y = x == y
    Yes _ == No _   = False
    No _  == Yes _  = False
    No _  == No _   = True  -- @'Not a' is a /h-Prop/ so all values are equal.

-- | 'decToBool' respects this ordering.
--
-- /Note:/ yet if you have @p :: a@ and @p :: 'Neg' a@, something is wrong.
--
instance Ord a => Ord (Dec a) where
    compare (Yes a) (Yes b) = compare a b
    compare (No _)  (Yes _) = compare False True
    compare (Yes _) (No _)  = compare True False
    compare (No _)  (No _)  = EQ

-- | Flip 'Dec' branches.
decNeg :: Dec a -> Dec (Neg a)
decNeg (Yes p) = No (toNegNeg p)
decNeg (No np) = Yes np

-- | Show 'Dec'.
--
-- >>> decShow $ Yes ()
-- "Yes ()"
--
-- >>> decShow $ No id
-- "No <toVoid>"
--
decShow :: Show a => Dec a -> String
decShow (Yes x) = "Yes " ++ showsPrec 11 x ""
decShow (No _)  = "No <toVoid>"

-- | Convert @'Dec' a@ to @'Maybe' a@, forgetting the 'No' evidence.
decToMaybe :: Dec a -> Maybe a
decToMaybe (Yes p) = Just p
decToMaybe (No _)  = Nothing

-- | Convert 'Dec' to 'Bool', forgetting the evidence.
decToBool :: Dec a -> Bool
decToBool (Yes _) = True
decToBool (No _)  = False
