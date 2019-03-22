module Data.Type.Dec where

import Data.Void (Void)

type Not a = a -> Void

-- | Decidable (nullary) relations.
data Dec a
    = Yes a
    | No (Not a)
