{-# LANGUAGE Trustworthy #-}
module TrustworthyCompat (
    (:~:) (..),
    TestEquality (..),
    coerce,
) where

import Data.Coerce        (coerce)
import Data.Type.Equality (TestEquality (..), (:~:) (..))
