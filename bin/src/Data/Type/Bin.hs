{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
#if MIN_VERSION_base(4,8,0)
{-# LANGUAGE Safe                 #-}
#else
{-# LANGUAGE Trustworthy          #-}
#endif
-- | Binary natural numbers. @DataKinds@ stuff.
module Data.Type.Bin (
    -- * Singleton
    SBin (..), SBinP (..),
    sbinToBin, BP.sbinpToBinP,
    sbinToNatural, BP.sbinpToNatural,
    -- * Implicit
    SBinI (..), SBinPI (..),
    withSBin, BP.withSBinP,
    reify,
    reflect,
    reflectToNum,
    -- * Type equality
    eqBin,
    EqBin,
    -- * Induction
    induction,
    -- * Arithmetic
    -- ** Successor
    Succ, Succ', Succ'',
    withSucc,
    -- ** Predecessor
    Pred,
    -- ** Addition
    Plus,
    -- ** Extras
    Mult2, Mult2Plus1,
    -- * Conversions
    -- ** To GHC Nat
    ToGHC, FromGHC,
    -- ** To fin Nat
    ToNat, FromNat,
    -- * Aliases
    Bin0, Bin1, Bin2, Bin3, Bin4, Bin5, Bin6, Bin7, Bin8, Bin9,
    ) where

import Control.DeepSeq   (NFData (..))
import Data.Bin          (Bin (..), BinP (..))
import Data.Boring       (Boring (..))
import Data.GADT.Compare (GEq (..))
import Data.GADT.DeepSeq (GNFData (..))
import Data.GADT.Show    (GShow (..))
import Data.Nat          (Nat (..))
import Data.Proxy        (Proxy (..))
import Data.Type.BinP    (SBinP (..), SBinPI (..))
import Data.Typeable     (Typeable)
import Numeric.Natural   (Natural)

#if MIN_VERSION_some(1,0,5)
import Data.EqP          (EqP (..))
import Data.GADT.Compare (defaultEq)
#endif

import qualified Data.Type.BinP as BP
import qualified Data.Type.Nat  as N
import qualified GHC.TypeLits   as GHC

import TrustworthyCompat

-- $setup
-- >>> :set -XDataKinds -XExplicitNamespaces -XTypeOperators
-- >>> import Data.Bin
-- >>> import Data.Type.BinP (BinP2, BinP3, BinP9)
-- >>> import Data.Nat (Nat (..))
-- >>> import Data.Type.Equality (type (==))
-- >>> import qualified Data.Type.BinP as BP
-- >>> import qualified Data.Type.Nat as N
-- >>> import qualified GHC.TypeLits as GHC

-------------------------------------------------------------------------------
-- Singletons
-------------------------------------------------------------------------------

-- | Singleton of 'Bin'.
data SBin (b :: Bin) where
    SBZ :: SBin 'BZ
    SBP :: SBinPI b => SBin ('BP b)
  deriving (Typeable)

deriving instance Show (SBin b)

-------------------------------------------------------------------------------
-- Implicits
-------------------------------------------------------------------------------

-- | Let constraint solver construct 'SBin'.
class                SBinI (b :: Bin) where sbin :: SBin b
instance             SBinI 'BZ        where sbin = SBZ
instance SBinPI b => SBinI ('BP b )   where sbin = SBP

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Construct 'SBinI' dictionary from 'SBin'.
withSBin :: SBin b -> (SBinI b => r) -> r
withSBin SBZ k = k
withSBin SBP k = k

-- | Reify 'Bin'
--
-- >>> reify bin3 reflect
-- 3
--
reify :: forall r. Bin -> (forall b. SBinI b => Proxy b -> r) -> r
reify BZ     k = k (Proxy :: Proxy 'BZ)
reify (BP b) k = BP.reify b (\(_ :: Proxy b) -> k (Proxy :: Proxy ('BP b)))

-- | Reflect type-level 'Bin' to the term level.
reflect :: forall b proxy. SBinI b => proxy b -> Bin
reflect p = case sbin :: SBin b of
    SBZ -> BZ
    SBP -> BP (aux p)
  where
    aux :: forall bn. SBinPI bn => proxy ('BP bn) -> BinP
    aux _ = BP.reflect (Proxy :: Proxy bn)

-- | Reflect type-level 'Bin' to the term level 'Num'.
reflectToNum :: forall b proxy a. (SBinI b, Num a) => proxy b -> a
reflectToNum p = case sbin :: SBin b of
    SBZ -> 0
    SBP -> aux p
  where
    aux :: forall bn. SBinPI bn => proxy ('BP bn) -> a
    aux _ = BP.reflectToNum (Proxy :: Proxy bn)

-- | Convert 'SBin' to 'Bin'.
sbinToBin :: forall n. SBin n -> Bin
sbinToBin SBZ   = BZ
sbinToBin s@SBP = aux s where
    aux :: forall m. SBinPI m => SBin ('BP m) -> Bin
    aux _ = BP (BP.sbinpToBinP (sbinp :: SBinP m))

-- | Convert 'SBin' to 'Natural'.
--
-- >>> sbinToNatural (sbin :: SBin Bin9)
-- 9
--
sbinToNatural :: forall n. SBin n -> Natural
sbinToNatural SBZ = 0
sbinToNatural s@SBP = aux s where
    aux :: forall m. SBinPI m => SBin ('BP m) -> Natural
    aux _ = BP.sbinpToNatural (sbinp :: SBinP m)

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

eqBin :: forall a b. (SBinI a, SBinI b) => Maybe (a :~: b)
eqBin = case (sbin :: SBin a, sbin :: SBin b) of
    (SBZ, SBZ) -> Just Refl
    (SBP, SBP) -> recur where
      recur :: forall n m. (SBinPI n, SBinPI m) => Maybe ('BP n :~: 'BP m)
      recur = do
          Refl <- BP.eqBinP :: Maybe (n :~: m)
          return Refl

    _          -> Nothing

instance TestEquality SBin where
    testEquality SBZ SBZ = Just Refl
    testEquality SBP SBP = recur where
        recur :: forall n m. (SBinPI n, SBinPI m) => Maybe ('BP n :~: 'BP m)
        recur = do
            Refl <- BP.eqBinP :: Maybe (n :~: m)
            return Refl
    testEquality _   _   = Nothing

-- | @since 0.1.2
type family EqBin (n :: Bin) (m :: Bin) where
    EqBin 'BZ     'BZ     = 'True
    EqBin ('BP n) ('BP m) = BP.EqBinP n m
    EqBin n       m       = 'False

#if !MIN_VERSION_base(4,11,0)
type instance n == m = EqBin n m
#endif

-------------------------------------------------------------------------------
-- Induction
-------------------------------------------------------------------------------

-- | Induction on 'Bin'.
induction
    :: forall b f. SBinI b
    => f 'BZ                                                     -- ^ \(P(0)\)
    -> f ('BP 'BE)                                               -- ^ \(P(1)\)
    -> (forall bb. SBinPI bb => f ('BP bb) -> f ('BP ('B0 bb)))  -- ^ \(\forall b. P(b) \to P(2b)\)
    -> (forall bb. SBinPI bb => f ('BP bb) -> f ('BP ('B1 bb)))  -- ^ \(\forall b. P(b) \to P(2b + 1)\)
    -> f b
induction z e o i = case sbin :: SBin b of
    SBZ -> z
    SBP -> go
  where
    go :: forall bb. SBinPI bb => f ('BP bb)
    go = case sbinp :: SBinP bb of
        SBE -> e
        SB0 -> o go
        SB1 -> i go

-------------------------------------------------------------------------------
-- Conversion to GHC Nat
-------------------------------------------------------------------------------

-- | Convert to GHC 'GHC.Nat'.
--
-- >>> :kind! ToGHC Bin5
-- ToGHC Bin5 :: GHC.Nat...
-- = 5
--
type family ToGHC (b :: Bin) :: GHC.Nat where
    ToGHC 'BZ     = 0
    ToGHC ('BP n) = BP.ToGHC n

-- | Convert from GHC 'GHC.Nat'.
--
-- >>> :kind! FromGHC 7
-- FromGHC 7 :: Bin
-- = 'BP ('B1 ('B1 'BE))
--
type family FromGHC (n :: GHC.Nat) :: Bin where
    FromGHC n = FromGHC' (GhcDivMod2 n)

type family FromGHC' (p :: (GHC.Nat, Bool)) :: Bin where
    FromGHC' '(0, 'False) = 'BZ
    FromGHC' '(0, 'True)  = 'BP 'BE
    FromGHC' '(n, 'False) = Mult2 (FromGHC n)
    FromGHC' '(n, 'True)  = 'BP (Mult2Plus1 (FromGHC n))

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
    ToNat ('BP n) = BP.ToNat n

-- | Convert from @fin@ 'Nat'.
--
-- >>> :kind! FromNat N.Nat5
-- FromNat N.Nat5 :: Bin
-- = 'BP ('B1 ('B0 'BE))
--
type family FromNat (n :: Nat) :: Bin where
    FromNat n = FromNat' (N.DivMod2 n)

type family FromNat' (p :: (Nat, Bool)) :: Bin where
    FromNat' '( 'Z, 'False) = 'BZ
    FromNat' '( 'Z, 'True)  = 'BP 'BE
    FromNat' '( n,  'False) = Mult2 (FromNat n)
    FromNat' '( n,  'True)  = 'BP (Mult2Plus1 (FromNat n))

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | Multiply by two.
--
-- >>> :kind! Mult2 Bin0 == Bin0
-- Mult2 Bin0 == Bin0 :: Bool
-- = 'True
--
-- >>> :kind! Mult2 Bin3 == Bin6
-- Mult2 Bin3 == Bin6 :: Bool
-- = 'True
--
type family Mult2 (b :: Bin) :: Bin where
    Mult2 'BZ     = 'BZ
    Mult2 ('BP n) = 'BP ('B0 n)

-- | Multiply by two and add one.
--
-- >>> :kind! Mult2Plus1 Bin0
-- Mult2Plus1 Bin0 :: BinP
-- = 'BE
--
-- >>> :kind! Mult2Plus1 Bin4 == BinP9
-- Mult2Plus1 Bin4 == BinP9 :: Bool
-- = 'True
--
type family Mult2Plus1 (b :: Bin) :: BinP where
    Mult2Plus1 'BZ     = 'BE
    Mult2Plus1 ('BP n) = ('B1 n)

-------------------------------------------------------------------------------
-- Arithmetic: Succ
-------------------------------------------------------------------------------

-- | Successor type family.
--
-- >>> :kind! Succ Bin5
-- Succ Bin5 :: Bin
-- = 'BP ('B0 ('B1 'BE))
--
-- @
-- `Succ`   :: 'Bin' -> 'Bin'
-- `Succ'`  :: 'Bin' -> 'BinP'
-- `Succ''` :: 'BinP' -> 'Bin'
-- @
type Succ b = 'BP (Succ' b)

type family Succ' (b :: Bin) :: BinP where
    Succ' 'BZ     = 'BE
    Succ' ('BP b) = BP.Succ b

type Succ'' b = 'BP (BP.Succ b)

withSucc :: forall b r. SBinI b => Proxy b -> (SBinPI (Succ' b) => r) -> r
withSucc p k = case sbin :: SBin b of
    SBZ -> k
    SBP -> withSucc' p k

withSucc' :: forall b r. SBinPI b => Proxy ('BP b) -> (SBinPI (BP.Succ b) => r) -> r
withSucc' _ k = BP.withSucc (Proxy :: Proxy b) k

-------------------------------------------------------------------------------
-- Predecessor
-------------------------------------------------------------------------------

-- | Predecessor type family..
--
-- >>> :kind! Pred BP.BinP1
-- Pred BP.BinP1 :: Bin
-- = 'BZ
--
-- >>> :kind! Pred BP.BinP5 == Bin4
-- Pred BP.BinP5 == Bin4 :: Bool
-- = 'True
--
-- >>> :kind! Pred BP.BinP8 == Bin7
-- Pred BP.BinP8 == Bin7 :: Bool
-- = 'True
--
-- >>> :kind! Pred BP.BinP6 == Bin5
-- Pred BP.BinP6 == Bin5 :: Bool
-- = 'True
--
type family Pred (b :: BinP) :: Bin where
    Pred 'BE     = 'BZ
    Pred ('B1 n) = 'BP ('B0 n)
    Pred ('B0 n) = 'BP (Pred' n)

type family Pred' (b :: BinP) :: BinP where
    Pred' 'BE     = 'BE
    Pred' ('B1 m) = 'B1 ('B0 m)
    Pred' ('B0 m) = 'B1 (Pred' m)

-------------------------------------------------------------------------------
-- Arithmetic: Plus
-------------------------------------------------------------------------------

-- | Addition.
--
-- >>> :kind! Plus Bin3 Bin3 == Bin6
-- Plus Bin3 Bin3 == Bin6 :: Bool
-- = 'True
--
-- >>> :kind! Mult2 Bin3 == Bin6
-- Mult2 Bin3 == Bin6 :: Bool
-- = 'True
--
type family Plus (a :: Bin) (b :: Bin) :: Bin where
    Plus 'BZ     b       = b
    Plus a       'BZ     = a
    Plus ('BP a) ('BP b) = 'BP (BP.Plus a b)

-------------------------------------------------------------------------------
-- Boring
-------------------------------------------------------------------------------

-- | @since 0.1.2
instance SBinI b => Boring (SBin b) where
    boring = sbin

-------------------------------------------------------------------------------
-- some
-------------------------------------------------------------------------------

-- | @since 0.1.3
instance Eq (SBin a) where
    _ == _ = True

-- | @since 0.1.3
instance Ord (SBin a) where
    compare _ _ = EQ

#if MIN_VERSION_some(1,0,5)
-- | @since 0.1.3
instance EqP SBin where eqp = defaultEq
#endif

-- | @since 0.1.2
instance GShow SBin where
    gshowsPrec = showsPrec

-- | @since 0.1.2
instance NFData (SBin n) where
    rnf SBZ = ()
    rnf SBP = ()

-- | @since 0.1.2
instance GNFData SBin where
    grnf = rnf

-- | @since 0.1.2
instance GEq SBin where
    geq = testEquality

-------------------------------------------------------------------------------
--- Aliases of Bin
-------------------------------------------------------------------------------

type Bin0 = 'BZ
type Bin1 = 'BP BP.BinP1
type Bin2 = 'BP BP.BinP2
type Bin3 = 'BP BP.BinP3
type Bin4 = 'BP BP.BinP4
type Bin5 = 'BP BP.BinP5
type Bin6 = 'BP BP.BinP6
type Bin7 = 'BP BP.BinP7
type Bin8 = 'BP BP.BinP8
type Bin9 = 'BP BP.BinP9
