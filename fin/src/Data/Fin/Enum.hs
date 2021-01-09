{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- |
--
-- This module is designed to be imported qualified:
--
-- @
-- import qualified Data.Fin.Enum as E
-- @
--
module Data.Fin.Enum (
    Enum (..),
    -- * Generic implementation
    gfrom, GFrom,
    gto, GTo,
    GEnumSize,
    ) where

import Prelude hiding (Enum (..))

import Data.Bifunctor (bimap)
import Data.Fin       (Fin (..))
import Data.Nat       (Nat (..))
import Data.Proxy     (Proxy (..))
import GHC.Generics   (M1 (..), U1 (..), V1, (:+:) (..))

import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Void     as V
import qualified GHC.Generics  as G

-- $setup
-- >>> import qualified Data.Fin as F

-- | Generic enumerations.
--
-- /Examples:/
--
-- >>> from ()
-- 0
--
-- >>> to 0 :: ()
-- ()
--
-- >>> to 0 :: Bool
-- False
--
-- >>> map to F.universe :: [Bool]
-- [False,True]
--
-- >>> map (to . (+1) . from) [LT, EQ, GT] :: [Ordering] -- Num Fin is modulo arithmetic
-- [EQ,GT,LT]
--
class Enum a where
    -- | The size of an enumeration.
    type EnumSize a :: Nat
    type EnumSize a = GEnumSize a

    -- | Converts a value to its index.
    from :: a -> Fin (EnumSize a)
    default from :: (G.Generic a, GFrom a, EnumSize a ~ GEnumSize a) => a -> Fin (EnumSize a)
    from = gfrom

    -- | Converts from index to the original value.
    to :: Fin (EnumSize a) -> a
    default to :: (G.Generic a, GTo a, EnumSize a ~ GEnumSize a) => Fin (EnumSize a) -> a
    to = gto

-- | 'Void' ~ 0
instance Enum V.Void where
    -- this should be written by hand to work with all @base@
    type EnumSize V.Void = N.Nat0
    from = V.absurd
    to   = F.absurd

-- | () ~ 1
instance Enum ()

-- | 'Bool' ~ 2
instance Enum Bool

-- | 'Ordering' ~ 3
instance Enum Ordering

-- | 'Either' ~ @+@
instance (Enum a, Enum b, N.SNatI (EnumSize a)) => Enum (Either a b) where
    type EnumSize (Either a b) = N.Plus (EnumSize a) (EnumSize b)

    to   = bimap to to . F.split
    from = F.append . bimap from from

-------------------------------------------------------------------------------
-- EnumSize
-------------------------------------------------------------------------------

-- | Compute the size from the type.
type GEnumSize a = EnumSizeRep (G.Rep a) N.Nat0

type family EnumSizeRep (a :: * -> *) (n :: Nat) :: Nat where
    EnumSizeRep (a :+: b )   n = EnumSizeRep a (EnumSizeRep b n)
    EnumSizeRep V1           n = n
    EnumSizeRep (M1 _d _c a) n = EnumSizeRep a n
    EnumSizeRep U1           n = 'S n
    -- No instance for K1 or :*:

-------------------------------------------------------------------------------
-- From
-------------------------------------------------------------------------------

-- | Generic version of 'from'.
gfrom :: (G.Generic a, GFrom a) => a -> Fin (GEnumSize a)
gfrom = \x -> gfromRep (G.from x) (Proxy :: Proxy N.Nat0)

-- | Constraint for the class that computes 'gfrom'.
type GFrom a = GFromRep (G.Rep a)

class GFromRep (a :: * -> *)  where
    gfromRep  :: a x     -> Proxy n -> Fin (EnumSizeRep a n)
    gfromSkip :: Proxy a -> Fin n   -> Fin (EnumSizeRep a n)

instance (GFromRep a, GFromRep b) => GFromRep (a :+: b) where
    gfromRep (L1 a) n = gfromRep a (prSkip n) where
        prSkip :: Proxy n -> Proxy (EnumSizeRep b n)
        prSkip  _ = Proxy
    gfromRep (R1 b) n = gfromSkip (Proxy :: Proxy a) (gfromRep b n)

    gfromSkip _ n = gfromSkip (Proxy :: Proxy a) (gfromSkip (Proxy :: Proxy b) n)

instance GFromRep a => GFromRep (M1 d c a) where
    gfromRep (M1 a) n = gfromRep a n
    gfromSkip _     n = gfromSkip (Proxy :: Proxy a) n

instance GFromRep V1 where
    gfromRep  v _ = case v of {}
    gfromSkip _ n = n

instance GFromRep U1 where
    gfromRep U1 _ = FZ
    gfromSkip _ n = FS n

-------------------------------------------------------------------------------
-- To
-------------------------------------------------------------------------------

-- | Generic version of 'to'.
gto :: (G.Generic a, GTo a) => Fin (GEnumSize a) -> a
gto = \x -> G.to $ gtoRep x id F.absurd

-- | Constraint for the class that computes 'gto'.
type GTo a = GToRep (G.Rep a)

class GToRep (a :: * -> *) where
    gtoRep :: Fin (EnumSizeRep a n) -> (a x -> r) -> (Fin n -> r) -> r

instance (GToRep a, GToRep b) => GToRep (a :+: b) where
    gtoRep n s k = gtoRep n (s . L1) $ \r -> gtoRep r (s . R1) k

instance GToRep a => GToRep (M1 d c a) where
    gtoRep n s = gtoRep n (s . M1)

instance GToRep V1 where
    gtoRep n _ k = k n

instance GToRep U1 where
    gtoRep FZ     s _ = s U1
    gtoRep (FS n) _ k = k n
