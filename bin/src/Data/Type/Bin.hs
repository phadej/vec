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
-- | Binary natural numbers. @DataKinds@ stuff.
module Data.Type.Bin (
    -- * Singleton
    SBin (..), SBinN (..),
    sbinToBin, sbinNToBinN,
    sbinToNatural, sbinNToNatural,
    -- * Implicit
    SBinI (..), SBinNI (..),
    withSBin, withSBinN,
    reify, reifyN,
    reflect, reflectN,
    reflectToNum, reflectNToNum,
    -- * Type equality
    eqBin, eqBinN,
    -- * Induction
    induction, inductionN,
    -- * Arithmetic
    -- ** Successor
    Succ, Succ', SuccN, SuccN',
    withSucc, withSuccN,
    -- ** Addition
    Plus, PlusN,
    -- ** Extras
    Mult2, Mult2Plus1,
    -- * Conversions
    -- ** To GHC Nat
    ToGHC, ToGHCN, FromGHC, FromGHCN,
    -- ** To fin Nat
    ToNat, ToNatN, FromNat,
    -- * Aliases
    -- ** Promoted Bin
    Bin0, Bin1, Bin2, Bin3, Bin4, Bin5, Bin6, Bin7, Bin8, Bin9,
    -- ** Promoted BinN
    BinN1, BinN2, BinN3, BinN4, BinN5, BinN6, BinN7, BinN8, BinN9,
    ) where

import Data.Bin           (Bin (..), BinN (..))
import Data.Coerce        (coerce)
import Data.Nat           (Nat (..))
import Data.Proxy         (Proxy (..))
import Data.Type.Equality ((:~:) (..), TestEquality (..))
import Data.Typeable      (Typeable)
import Numeric.Natural    (Natural)

import qualified Data.Type.Nat as N
import qualified GHC.TypeLits  as GHC

-- $setup
-- >>> :set -XDataKinds
-- >>> import Data.Bin

-------------------------------------------------------------------------------
-- Singletons
-------------------------------------------------------------------------------

-- | Singleton of 'Bin'.
data SBin (b :: Bin) where
    SBZ :: SBin 'BZ
    SBN :: SBinNI b => SBin ('BN b)
  deriving (Typeable)

-- | Singleton of 'BinN'.
data SBinN (b :: BinN) where
    SBE :: SBinN 'BE
    SB0 :: SBinNI b => SBinN ('B0 b)
    SB1 :: SBinNI b => SBinN ('B1 b)
  deriving (Typeable)

-------------------------------------------------------------------------------
-- Implicits
-------------------------------------------------------------------------------

-- | Let constraint solver construct 'SBin'.
class                SBinI (b :: Bin) where sbin :: SBin b
instance             SBinI 'BZ        where sbin = SBZ
instance SBinNI b => SBinI ('BN b )   where sbin = SBN

-- | Let constraint solver construct 'SBinN'.
class                SBinNI (b :: BinN) where sbinN :: SBinN b
instance             SBinNI 'BE          where sbinN = SBE
instance SBinNI b => SBinNI ('B0 b)      where sbinN = SB0
instance SBinNI b => SBinNI ('B1 b)      where sbinN = SB1

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Construct 'SBinI' dictionary from 'SBin'.
withSBin :: SBin b -> (SBinI b => r) -> r
withSBin SBZ k = k
withSBin SBN k = k

-- | Construct 'SBinNI' dictionary from 'SBinN'.
withSBinN :: SBinN b -> (SBinNI b => r) -> r
withSBinN SBE k = k
withSBinN SB0 k = k
withSBinN SB1 k = k

-- | Reify 'Bin'
--
-- >>> reify bin3 reflect
-- 3
--
reify :: forall r. Bin -> (forall b. SBinI b => Proxy b -> r) -> r
reify BZ     k = k (Proxy :: Proxy 'BZ)
reify (BN b) k = reifyN b (\(_ :: Proxy b) -> k (Proxy :: Proxy ('BN b)))

-- | Reify 'BinN'.
reifyN :: forall r. BinN -> (forall b. SBinNI b => Proxy b -> r) -> r
reifyN BE     k = k (Proxy :: Proxy 'BE)
reifyN (B0 b) k = reifyN b (\(_ :: Proxy b) -> k (Proxy :: Proxy ('B0 b)))
reifyN (B1 b) k = reifyN b (\(_ :: Proxy b) -> k (Proxy :: Proxy ('B1 b)))

-- | Reflect type-level 'Bin' to the term level.
reflect :: forall b proxy. SBinI b => proxy b -> Bin
reflect p = case sbin :: SBin b of
    SBZ -> BZ
    SBN -> BN (aux p)
  where
    aux :: forall bn. SBinNI bn => proxy ('BN bn) -> BinN
    aux _ = reflectN (Proxy :: Proxy bn)

-- | Reflect type-level 'BinN' to the term level.
reflectN :: forall b proxy. SBinNI b => proxy b -> BinN
reflectN _ = unKN (inductionN (KN BE) (mapKN B0) (mapKN B1) :: KN BinN b)

-- | Reflect type-level 'Bin' to the term level 'Num'.
reflectToNum :: forall b proxy a. (SBinI b, Num a) => proxy b -> a
reflectToNum p = case sbin :: SBin b of
    SBZ -> 0
    SBN -> aux p
  where
    aux :: forall bn. SBinNI bn => proxy ('BN bn) -> a
    aux _ = reflectNToNum (Proxy :: Proxy bn)

-- | Reflect type-level 'BinN' to the term level 'Num'.
reflectNToNum :: forall b proxy a. (SBinNI b, Num a) => proxy b -> a
reflectNToNum _ = unKN (inductionN (KN 1) (mapKN (2*)) (mapKN (\x -> 2 * x + 1)) :: KN a b)

-- | Convert 'SBin' to 'Bin'
sbinToBin :: forall n. SBin n -> Bin
sbinToBin SBZ   = BZ
sbinToBin s@SBN = aux s where
    aux :: forall m. SBinNI m => SBin ('BN m) -> Bin
    aux _ = BN (sbinNToBinN (sbinN :: SBinN m))

sbinNToBinN :: forall n. SBinN n -> BinN
sbinNToBinN s = withSBinN s $ reflectN (Proxy :: Proxy n)

-- | Convert 'SBin' to 'Natural'
--
-- >>> sbinToNatural (sbin :: SBin Bin9)
-- 9
--
sbinToNatural :: forall n. SBin n -> Natural
sbinToNatural SBZ = 0
sbinToNatural s@SBN = aux s where
    aux :: forall m. SBinNI m => SBin ('BN m) -> Natural
    aux _ = sbinNToNatural (sbinN :: SBinN m)

-- | Convert 'SBinN' to 'Natural'
--
-- >>> sbinNToNatural (sbinN :: SBinN BinN8)
-- 8
--
sbinNToNatural :: forall n. SBinN n -> Natural
sbinNToNatural s = withSBinN s $ unKN (inductionN
    (KN 1)
    (mapKN (2 *))
    (mapKN (\x -> succ (2 * x))) :: KN Natural n)

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

eqBin :: forall a b. (SBinI a, SBinI b) => Maybe (a :~: b)
eqBin = case (sbin :: SBin a, sbin :: SBin b) of
    (SBZ, SBZ) -> Just Refl
    (SBN, SBN) -> recur where
      recur :: forall n m. (SBinNI n, SBinNI m) => Maybe ('BN n :~: 'BN m)
      recur = do
          Refl <- eqBinN :: Maybe (n :~: m)
          return Refl

    _          -> Nothing

eqBinN :: forall a b. (SBinNI a, SBinNI b) => Maybe (a :~: b)
eqBinN = case (sbinN :: SBinN a, sbinN :: SBinN b) of
    (SBE, SBE) -> Just Refl
    (SB0, SB0) -> recur where
        recur :: forall n m. (SBinNI n, SBinNI m) => Maybe ('B0 n :~: 'B0 m)
        recur = do
            Refl <- eqBinN :: Maybe (n :~: m)
            return Refl
    (SB1, SB1) -> recur where
        recur :: forall n m. (SBinNI n, SBinNI m) => Maybe ('B1 n :~: 'B1 m)
        recur = do
            Refl <- eqBinN :: Maybe (n :~: m)
            return Refl
    _ -> Nothing

instance TestEquality SBin where
    testEquality SBZ SBZ = Just Refl
    testEquality SBN SBN = recur where
        recur :: forall n m. (SBinNI n, SBinNI m) => Maybe ('BN n :~: 'BN m)
        recur = do
            Refl <- eqBinN :: Maybe (n :~: m)
            return Refl
    testEquality _   _   = Nothing

instance TestEquality SBinN where
    testEquality SBE SBE = Just Refl
    testEquality SB0 SB0 = eqBinN
    testEquality SB1 SB1 = eqBinN

    testEquality _ _ = Nothing

-------------------------------------------------------------------------------
-- Induction
-------------------------------------------------------------------------------

-- | Induction on 'Bin'.
induction
    :: forall b f. SBinI b
    => f 'BZ                                                     -- ^ \(P(0)\)
    -> f ('BN 'BE)                                               -- ^ \(P(1)\)
    -> (forall bb. SBinNI bb => f ('BN bb) -> f ('BN ('B0 bb)))  -- ^ \(\forall b. P(b) \to P(2b)\)
    -> (forall bb. SBinNI bb => f ('BN bb) -> f ('BN ('B1 bb)))  -- ^ \(\forall b. P(b) \to P(2b + 1)\)
    -> f b
induction z e o i = case sbin :: SBin b of
    SBZ -> z
    SBN -> go
  where
    go :: forall bb. SBinNI bb => f ('BN bb)
    go = case sbinN :: SBinN bb of
        SBE -> e
        SB0 -> o go
        SB1 -> i go

-- | Induction on 'BinN'.
inductionN
    :: forall b f. SBinNI b
    => f 'BE                                         -- ^ \(P(1)\)
    -> (forall bb. SBinNI bb => f bb -> f ('B0 bb))  -- ^ \(\forall b. P(b) \to P(2b)\)
    -> (forall bb. SBinNI bb => f bb -> f ('B1 bb))  -- ^ \(\forall b. P(b) \to P(2b + 1)\)
    -> f b
inductionN e o i = go where
    go :: forall bb. SBinNI bb => f bb
    go = case sbinN :: SBinN bb of
        SBE -> e
        SB0 -> o go
        SB1 -> i go

-------------------------------------------------------------------------------
-- Conversion to GHC Nat
-------------------------------------------------------------------------------

-- | Convert to GHC 'GHC.Nat'.
--
-- >>> :kind! ToGHC Bin5
-- ToGHC Bin5 :: GHC.Nat
-- = 5
--
type family ToGHC (b :: Bin) :: GHC.Nat where
    ToGHC 'BZ     = 0
    ToGHC ('BN n) = ToGHCN n

type family ToGHCN (b :: BinN) :: GHC.Nat where
    ToGHCN 'BE = 1
    ToGHCN ('B0 b) = 2 GHC.* (ToGHCN b)
    ToGHCN ('B1 b) = 1 GHC.+ 2 GHC.* (ToGHCN b)

-- | Convert from GHC 'GHC.Nat'.
--
-- >>> :kind! FromGHC 7
-- FromGHC 7 :: Bin
-- = 'BN ('B1 ('B1 'BE))
--
type family FromGHC (n :: GHC.Nat) :: Bin where
    FromGHC n = FromGHC' (GhcDivMod2 n)

type family FromGHC' (p :: (GHC.Nat, Bool)) :: Bin where
    FromGHC' '(0, 'False) = 'BZ
    FromGHC' '(0, 'True)  = 'BN 'BE
    FromGHC' '(n, 'False) = Mult2 (FromGHC n)
    FromGHC' '(n, 'True)  = Mult2Plus1 (FromGHC n)

type family FromGHCN (n :: GHC.Nat) :: BinN where
    FromGHCN n = FromGHCN' (FromGHC n)

type family FromGHCN' (b :: Bin) :: BinN where
    FromGHCN' ('BN b) = b

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

-------------------------------------------------------------------------------
-- Conversion to Nat
-------------------------------------------------------------------------------

-- | Convert to @fin@ 'Nat'.
--
-- >>> :kind! ToNat Bin5
-- ToNat Bin5 :: Nat
-- = 'S ('S ('S ('S ('S 'Z))))
--
type family ToNat (b :: Bin) :: Nat where
    ToNat 'BZ     = 'Z
    ToNat ('BN n) = ToNatN n

type family ToNatN (b :: BinN) :: Nat where
    ToNatN 'BE     = 'S 'Z
    ToNatN ('B0 b) = N.Mult2 (ToNatN b)
    ToNatN ('B1 b) = 'S (N.Mult2 (ToNatN b))

-- | Convert from @fin@ 'Nat'.
--
-- >>> :kind! FromNat N.Nat5
-- FromNat N.Nat5 :: Bin
-- = 'BN ('B1 ('B0 'BE))
--
type family FromNat (n :: Nat) :: Bin where
    FromNat n = FromNat' (N.DivMod2 n)

type family FromNat' (p :: (Nat, Bool)) :: Bin where
    FromNat' '( 'Z, 'False) = 'BZ
    FromNat' '( 'Z, 'True)  = 'BN 'BE
    FromNat' '( n,  'False) = Mult2 (FromNat n)
    FromNat' '( n,  'True)  = Mult2Plus1 (FromNat n)

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | Multiply by two.
--
-- >>> :kind! Mult2 Bin0
-- Mult2 Bin0 :: Bin
-- = 'BZ
--
-- >>> :kind! Mult2 Bin7
-- Mult2 Bin7 :: Bin
-- = 'BN ('B0 ('B1 BinN3))
type family Mult2 (b :: Bin) :: Bin where
    Mult2 'BZ     = 'BZ
    Mult2 ('BN n) = 'BN ('B0 n)

-- | Multiply by two and add one.
--
-- >>> :kind! Mult2Plus1 Bin0
-- Mult2Plus1 Bin0 :: Bin
-- = 'BN 'BE
--
-- >>> :kind! Mult2Plus1 Bin5
-- Mult2Plus1 Bin5 :: Bin
-- = 'BN ('B1 ('B1 BinN2))
type family Mult2Plus1 (b :: Bin) :: Bin where
    Mult2Plus1 'BZ     = 'BN 'BE
    Mult2Plus1 ('BN n) = 'BN ('B1 n)

-------------------------------------------------------------------------------
-- Arithmetic: Succ
-------------------------------------------------------------------------------

-- | Successor type family.
--
-- >>> :kind! Succ Bin5
-- Succ Bin5 :: Bin
-- = 'BN ('B0 ('B1 'BE))
--
type Succ b = 'BN (Succ' b)

type SuccN b = 'BN (SuccN' b)

type family Succ' (b :: Bin) :: BinN where
    Succ' 'BZ     = 'BE
    Succ' ('BN b) = SuccN' b

type family SuccN' (b :: BinN) :: BinN where
    SuccN' 'BE     = 'B0 'BE
    SuccN' ('B0 n) = 'B1 n
    SuccN' ('B1 n) = 'B0 (SuccN' n)

withSucc :: forall b r. SBinI b => Proxy b -> (SBinNI (Succ' b) => r) -> r
withSucc p k = case sbin :: SBin b of
    SBZ -> k
    SBN -> withSuccN' p k

withSuccN' :: forall b r. SBinNI b => Proxy ('BN b) -> (SBinNI (SuccN' b) => r) -> r
withSuccN' _ k = withSuccN (Proxy :: Proxy b) k

withSuccN :: forall b r. SBinNI b => Proxy b -> (SBinNI (SuccN' b) => r) -> r
withSuccN p k = case sbinN :: SBinN b of
    SBE -> k
    SB0 -> k
    SB1 -> recur p k
  where
    -- eta needed for older GHC
    recur :: forall m s. SBinNI m => Proxy ('B1 m) -> (SBinNI ('B0 (SuccN' m)) => s) -> s
    recur _ k' = withSuccN (Proxy :: Proxy m) k'

-------------------------------------------------------------------------------
-- Arithmetic: Plus
-------------------------------------------------------------------------------

-- | Addition.
--
-- >>> :kind! Plus Bin7 Bin7
-- Plus Bin7 Bin7 :: Bin
-- = 'BN ('B0 ('B1 ('B1 'BE)))
--
-- >>> :kind! Mult2 Bin7
-- Mult2 Bin7 :: Bin
-- = 'BN ('B0 ('B1 BinN3))
--
type family Plus (a :: Bin) (b :: Bin) :: Bin where
    Plus 'BZ     b       = b
    Plus a       'BZ     = a
    Plus ('BN a) ('BN b) = 'BN (PlusN a b)

type family PlusN (a :: BinN) (b :: BinN) :: BinN where
    PlusN 'BE     b       = SuccN' b
    PlusN a       'BE     = SuccN' a
    PlusN ('B0 a) ('B0 b) = 'B0 (PlusN a b)
    PlusN ('B1 a) ('B0 b) = 'B1 (PlusN a b)
    PlusN ('B0 a) ('B1 b) = 'B1 (PlusN a b)
    PlusN ('B1 a) ('B1 b) = 'B0 (SuccN' (PlusN a b))

-------------------------------------------------------------------------------
--- Aliases of Bin
-------------------------------------------------------------------------------

type Bin0 = 'BZ
type Bin1 = 'BN BinN1
type Bin2 = 'BN BinN2
type Bin3 = 'BN BinN3
type Bin4 = 'BN BinN4
type Bin5 = 'BN BinN5
type Bin6 = 'BN BinN6
type Bin7 = 'BN BinN7
type Bin8 = 'BN BinN8
type Bin9 = 'BN BinN9

-------------------------------------------------------------------------------
-- Aliases of BinN
-------------------------------------------------------------------------------

type BinN1 = 'BE
type BinN2 = 'B0 BinN1
type BinN3 = 'B1 BinN1
type BinN4 = 'B0 BinN2
type BinN5 = 'B1 BinN2
type BinN6 = 'B0 BinN3
type BinN7 = 'B1 BinN3
type BinN8 = 'B0 BinN4
type BinN9 = 'B1 BinN4

-------------------------------------------------------------------------------
-- Aux
-------------------------------------------------------------------------------

newtype KN a (b :: BinN) = KN a

unKN :: KN a b -> a
unKN = coerce

mapKN :: (a -> b) -> KN a bn -> KN b bn'
mapKN = coerce
