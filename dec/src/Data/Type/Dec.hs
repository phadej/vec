{-# LANGUAGE Safe #-}
module Data.Type.Dec (
    -- * Types
    Neg,
    Dec (..),
    Decidable (..),
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

    -- * Boring
    -- | @'Dec' a@ can be 'Boring' in two ways: When 'a' is 'Boring' or 'Absurd'.
    boringYes,
    absurdNo,
    ) where

import Data.Void (Void)
import Data.Boring (Absurd (..), Boring (..))

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

-------------------------------------------------------------------------------
-- Boring
-------------------------------------------------------------------------------

-- | This relies on the fact that @a@ is /proposition/ in h-Prop sense.
--
-- @since 0.1.3
instance Decidable a => Boring (Dec a) where
    boring = decide
-- | 'Yes', it's 'boring'.
--
-- @since 0.0.5
boringYes :: Boring a => Dec a
boringYes = Yes boring

-- | 'No', it's 'absurd'.
--
-- @since 0.0.5
absurdNo :: Absurd a => Dec a
absurdNo = No absurd
