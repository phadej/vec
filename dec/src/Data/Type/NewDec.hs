{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE EmptyCase     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Type.NewDec (
    -- * Types
    Neg,
    Dec (..),
    Reflects (..),
    Decidable (..),
    -- * Neg combinators
    toNegNeg,
    tripleNeg,
    contradict,
    contraposition,
    -- * Boolean
    discreteBool,
    -- * Dec combinators
    decNeg,
    decMap,
    decShow,
    decToMaybe,
    decToBool,
    ) where

import Data.Kind            (Type)
import Data.Singletons.Bool (SBool (..), fromSBool)
import Data.Type.Equality   ((:~:) (..))
import Data.Void            (Void)

-- | Intuitionistic negation.
type Neg a = a -> Void

-- | Reflects idiom.
-- 
-- The truth value of @p@ is reflected
data family Reflects :: Type -> Bool -> Type
newtype instance Reflects a 'True  = OfYes a
newtype instance Reflects a 'False = OfNo (a -> Void)

-- | Decidable (nullary) relations.
data Dec p where
    Because :: SBool does -> Reflects p does -> Dec p

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
--
-------------------------------------------------------------------------------

discreteBool :: SBool a -> SBool b -> Dec (a :~: b)
discreteBool STrue  STrue  = STrue  `Because` OfYes Refl
discreteBool SFalse SFalse = STrue  `Because` OfYes Refl
discreteBool STrue  SFalse = SFalse `Because` OfNo (\p -> case p of {})
discreteBool SFalse STrue  = SFalse `Because` OfNo (\p -> case p of {})


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

{-
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
-}

decMap :: forall a b. (a -> b) -> (b -> a) -> Dec a -> Dec b
decMap f g (Because does proof) = Because does (go does proof) where
    go :: SBool does -> Reflects a does -> Reflects b does
    go STrue (OfYes p) = OfYes (f p)
    go SFalse (OfNo p) = OfNo (p . g)

-- | Flip 'Dec' branches.
decNeg :: Dec a -> Dec (Neg a)
decNeg (Because STrue (OfYes p))   = Because SFalse (OfNo (toNegNeg p))
decNeg (Because SFalse (OfNo np)) = Because STrue (OfYes np)

-- | Show 'Dec'.
--
-- >>> decShow $ Yes ()
-- "Yes ()"
--
-- >>> decShow $ No id
-- "No <toVoid>"
--
decShow :: Show a => Dec a -> String
decShow (Because STrue (OfYes x)) = "Yes " ++ showsPrec 11 x ""
decShow _                         = "No <toVoid>"

-- | Convert @'Dec' a@ to @'Maybe' a@, forgetting the 'No' evidence.
decToMaybe :: Dec a -> Maybe a
decToMaybe (Because STrue (OfYes p)) = Just p
decToMaybe _                         = Nothing

-- | Convert 'Dec' to 'Bool', forgetting the evidence.
decToBool :: Dec a -> Bool
decToBool (Because b _) = fromSBool b
