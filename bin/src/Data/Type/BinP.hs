{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
#if MIN_VERSION_base(4,8,0)
{-# LANGUAGE Safe                 #-}
#else
{-# LANGUAGE Trustworthy          #-}
#endif
-- | Positive binary natural numbers. @DataKinds@ stuff.
module Data.Type.BinP (
    -- * Singleton
    SBinP (..),
    sbinpToBinP,
    sbinpToNatural,
    -- * Implicit
    SBinPI (..),
    withSBinP,
    reify,
    reflect,
    reflectToNum,
    -- * Type equality
    eqBinP,
    -- * Induction
    induction,
    -- * Arithmetic
    -- ** Successor
    Succ,
    withSucc,
    -- ** Addition
    Plus,
    -- * Conversions
    -- ** To GHC Nat
    ToGHC, FromGHC,
    -- ** To fin Nat
    ToNat,
    -- * Aliases
    BinP1, BinP2, BinP3, BinP4, BinP5, BinP6, BinP7, BinP8, BinP9,
    ) where

import Data.BinP       (BinP (..))
import Data.Boring     (Boring (..))
import Data.Nat        (Nat (..))
import Data.Proxy      (Proxy (..))
import Data.Typeable   (Typeable)
import Numeric.Natural (Natural)

import qualified Data.Type.Nat as N
import qualified GHC.TypeLits  as GHC

import TrustworthyCompat

-- $setup
-- >>> :set -XDataKinds
-- >>> import Data.Bin

-------------------------------------------------------------------------------
-- Singletons
-------------------------------------------------------------------------------

-- | Singleton of 'BinP'.
data SBinP (b :: BinP) where
    SBE :: SBinP 'BE
    SB0 :: SBinPI b => SBinP ('B0 b)
    SB1 :: SBinPI b => SBinP ('B1 b)
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Implicits
-------------------------------------------------------------------------------

-- | Let constraint solver construct 'SBinP'.
class                SBinPI (b :: BinP) where sbinp :: SBinP b
instance             SBinPI 'BE          where sbinp = SBE
instance SBinPI b => SBinPI ('B0 b)      where sbinp = SB0
instance SBinPI b => SBinPI ('B1 b)      where sbinp = SB1

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Construct 'SBinPI' dictionary from 'SBinP'.
withSBinP :: SBinP b -> (SBinPI b => r) -> r
withSBinP SBE k = k
withSBinP SB0 k = k
withSBinP SB1 k = k

-- | Reify 'BinP'.
reify :: forall r. BinP -> (forall b. SBinPI b => Proxy b -> r) -> r
reify BE     k = k (Proxy :: Proxy 'BE)
reify (B0 b) k = reify b (\(_ :: Proxy b) -> k (Proxy :: Proxy ('B0 b)))
reify (B1 b) k = reify b (\(_ :: Proxy b) -> k (Proxy :: Proxy ('B1 b)))

-- | Reflect type-level 'BinP' to the term level.
reflect :: forall b proxy. SBinPI b => proxy b -> BinP
reflect _ = unKP (induction (KP BE) (mapKP B0) (mapKP B1) :: KP BinP b)

-- | Reflect type-level 'BinP' to the term level 'Num'.
reflectToNum :: forall b proxy a. (SBinPI b, Num a) => proxy b -> a
reflectToNum _ = unKP (induction (KP 1) (mapKP (2*)) (mapKP (\x -> 2 * x + 1)) :: KP a b)

-- | Cconvert 'SBinP' to 'BinP'.
sbinpToBinP :: forall n. SBinP n -> BinP
sbinpToBinP s = withSBinP s $ reflect (Proxy :: Proxy n)

-- | Convert 'SBinP' to 'Natural'.
--
-- >>> sbinpToNatural (sbinp :: SBinP BinP8)
-- 8
--
sbinpToNatural :: forall n. SBinP n -> Natural
sbinpToNatural s = withSBinP s $ unKP (induction
    (KP 1)
    (mapKP (2 *))
    (mapKP (\x -> succ (2 * x))) :: KP Natural n)

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

eqBinP :: forall a b. (SBinPI a, SBinPI b) => Maybe (a :~: b)
eqBinP = case (sbinp :: SBinP a, sbinp :: SBinP b) of
    (SBE, SBE) -> Just Refl
    (SB0, SB0) -> recur where
        recur :: forall n m. (SBinPI n, SBinPI m) => Maybe ('B0 n :~: 'B0 m)
        recur = do
            Refl <- eqBinP :: Maybe (n :~: m)
            return Refl
    (SB1, SB1) -> recur where
        recur :: forall n m. (SBinPI n, SBinPI m) => Maybe ('B1 n :~: 'B1 m)
        recur = do
            Refl <- eqBinP :: Maybe (n :~: m)
            return Refl
    _ -> Nothing

instance TestEquality SBinP where
    testEquality SBE SBE = Just Refl
    testEquality SB0 SB0 = eqBinP
    testEquality SB1 SB1 = eqBinP

    testEquality _ _ = Nothing

-------------------------------------------------------------------------------
-- Convert to GHC Nat
-------------------------------------------------------------------------------

type family ToGHC (b :: BinP) :: GHC.Nat where
    ToGHC 'BE = 1
    ToGHC ('B0 b) = 2 GHC.* (ToGHC b)
    ToGHC ('B1 b) = 1 GHC.+ 2 GHC.* (ToGHC b)

type family FromGHC (n :: GHC.Nat) :: BinP where
    FromGHC n = FromGHC' (FromGHCMaybe n)

-- internals

type family FromGHC' (b :: Maybe BinP) :: BinP where
    FromGHC' ('Just b) = b

type family FromGHCMaybe (n :: GHC.Nat) :: Maybe BinP where
    FromGHCMaybe n = FromGHCMaybe' (GhcDivMod2 n)

type family FromGHCMaybe' (p :: (GHC.Nat, Bool)) :: Maybe BinP where
    FromGHCMaybe' '(0, 'False) = 'Nothing
    FromGHCMaybe' '(0, 'True)  = 'Just 'BE
    FromGHCMaybe' '(n, 'False) = Mult2 (FromGHCMaybe n)
    FromGHCMaybe' '(n, 'True)  = 'Just (Mult2Plus1 (FromGHCMaybe n))

-- | >>> :kind! GhcDivMod2 13
-- GhcDivMod2 13 :: (GHC.Nat, Bool)
-- = '(6, 'True)
--
type family GhcDivMod2 (n :: GHC.Nat) :: (GHC.Nat, Bool) where
    GhcDivMod2 0 = '(0, 'False)
    GhcDivMod2 1 = '(0, 'True)
    GhcDivMod2 n = GhcDivMod2' (GhcDivMod2 (n GHC.- 2))

type family GhcDivMod2' (p :: (GHC.Nat, Bool)) :: (GHC.Nat, Bool) where
    GhcDivMod2' '(n, b) = '(1 GHC.+ n, b)

type family Mult2 (b :: Maybe BinP) :: Maybe BinP where
    Mult2 'Nothing  = 'Nothing
    Mult2 ('Just n) = 'Just ('B0 n)

type family Mult2Plus1 (b :: Maybe BinP) :: BinP where
    Mult2Plus1 'Nothing  = 'BE
    Mult2Plus1 ('Just n) = ('B1 n)

-------------------------------------------------------------------------------
-- Conversion to Nat
-------------------------------------------------------------------------------

type family ToNat (b :: BinP) :: Nat where
    ToNat 'BE     = 'S 'Z
    ToNat ('B0 b) = N.Mult2 (ToNat b)
    ToNat ('B1 b) = 'S (N.Mult2 (ToNat b))

-------------------------------------------------------------------------------
-- Arithmetic: Succ
-------------------------------------------------------------------------------

type family Succ (b :: BinP) :: BinP where
    Succ 'BE     = 'B0 'BE
    Succ ('B0 n) = 'B1 n
    Succ ('B1 n) = 'B0 (Succ n)

withSucc :: forall b r. SBinPI b => Proxy b -> (SBinPI (Succ b) => r) -> r
withSucc p k = case sbinp :: SBinP b of
    SBE -> k
    SB0 -> k
    SB1 -> recur p k
  where
    -- eta needed for older GHC
    recur :: forall m s. SBinPI m => Proxy ('B1 m) -> (SBinPI ('B0 (Succ m)) => s) -> s
    recur _ k' = withSucc (Proxy :: Proxy m) k'

-------------------------------------------------------------------------------
-- Arithmetic: Plus
-------------------------------------------------------------------------------

type family Plus (a :: BinP) (b :: BinP) :: BinP where
    Plus 'BE     b       = Succ b
    Plus a       'BE     = Succ a
    Plus ('B0 a) ('B0 b) = 'B0 (Plus a b)
    Plus ('B1 a) ('B0 b) = 'B1 (Plus a b)
    Plus ('B0 a) ('B1 b) = 'B1 (Plus a b)
    Plus ('B1 a) ('B1 b) = 'B0 (Succ (Plus a b))

-------------------------------------------------------------------------------
-- Induction
-------------------------------------------------------------------------------

-- | Induction on 'BinP'.
induction
    :: forall b f. SBinPI b
    => f 'BE                                         -- ^ \(P(1)\)
    -> (forall bb. SBinPI bb => f bb -> f ('B0 bb))  -- ^ \(\forall b. P(b) \to P(2b)\)
    -> (forall bb. SBinPI bb => f bb -> f ('B1 bb))  -- ^ \(\forall b. P(b) \to P(2b + 1)\)
    -> f b
induction e o i = go where
    go :: forall bb. SBinPI bb => f bb
    go = case sbinp :: SBinP bb of
        SBE -> e
        SB0 -> o go
        SB1 -> i go

-------------------------------------------------------------------------------
-- Boring
-------------------------------------------------------------------------------

-- | @since 0.1.2
instance SBinPI b => Boring (SBinP b) where
    boring = sbinp

-------------------------------------------------------------------------------
-- Aliases of BinP
-------------------------------------------------------------------------------

type BinP1 = 'BE
type BinP2 = 'B0 BinP1
type BinP3 = 'B1 BinP1
type BinP4 = 'B0 BinP2
type BinP5 = 'B1 BinP2
type BinP6 = 'B0 BinP3
type BinP7 = 'B1 BinP3
type BinP8 = 'B0 BinP4
type BinP9 = 'B1 BinP4

-------------------------------------------------------------------------------
-- Aux
-------------------------------------------------------------------------------

newtype KP a (b :: BinP) = KP a

unKP :: KP a b -> a
unKP = coerce

mapKP :: (a -> b) -> KP a bn -> KP b bn'
mapKP = coerce
