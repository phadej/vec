{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE Trustworthy        #-}
module TrustworthyCompat (
    (:~:) (..),
    TestEquality (..),
    coerce,
    type (==),
) where

import Data.Coerce        (coerce)
import Data.Type.Equality (TestEquality (..), type (==), (:~:) (..))
