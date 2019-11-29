{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
module Data.RAL.Pos (
    Pos (..),
    PosN (..),
    -- * Top & Pop
    top, pop, Pop,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    explicitShowN,
    explicitShowsPrecN,
    -- * Conversions
    toNatural,
    -- * Interesting
    absurd,
    boring,
    -- * Weakening (succ)
    weakenRight1, weakenRight1N,
    ) where

import Prelude
       (Bool (..), Bounded (..), Eq, Int, Ord (..), Ordering (..), Show (..),
       ShowS, String, showParen, showString, ($), (*), (+), (.))

import Control.Applicative (pure)
import Data.Bin            (Bin (..), BinN (..))
import Data.Foldable       (foldl)
import Data.Nat            (Nat (..))
import Data.Proxy          (Proxy (..))
import Data.Typeable       (Typeable)
import Data.Vec.Lazy       (Vec (..))
import Numeric.Natural     (Natural)

import qualified Data.Type.Nat as N

import Data.Type.Bin

-- $setup
-- >>> import Prelude (fmap)
-- >>> import Data.RAL

-- | 'Pos' is to 'Bin' is what 'Fin' is to 'Nat'.
data Pos (b :: Bin) where
    Pos :: PosN 'Z b -> Pos ('BN b)
  deriving (Typeable)

-- | 'PosN' is to 'BinN' is what 'Fin' is to 'Nat', when 'n' is 'Z'.
data PosN (n :: Nat) (b :: BinN) where
    AtEnd  :: Vec n Bool    -> PosN n 'BE      -- ^ position is either at the last digit;
    Here   :: Vec n Bool    -> PosN n ('B1 b)  -- ^ somewhere here
    There1 :: PosN ('S n) b -> PosN n ('B1 b)  -- ^ or there, if the bit is one;
    There0 :: PosN ('S n) b -> PosN n ('B0 b)  -- ^ or only there if it is none.
  deriving (Typeable)

deriving instance Eq (Pos b)
deriving instance Ord (Pos b)

deriving instance Eq (PosN n b)
instance Ord (PosN n b) where
    compare (AtEnd  x) (AtEnd  y) = compare x y
    compare (Here   x) (Here   y) = compare x y
    compare (Here   _) (There1 _) = LT
    compare (There1 _) (Here   _) = GT
    compare (There1 x) (There1 y) = compare x y
    compare (There0 x) (There0 y) = compare x y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (Pos b) where
    showsPrec d = showsPrec d . toNatural

-- |
--
-- >>> minBound < (maxBound :: Pos Bin5)
-- True
instance (SBinNI n, b ~ 'BN n) => Bounded (Pos b) where
    minBound = Pos minBound
    maxBound = Pos maxBound

instance (N.SNatI n, SBinNI b) => Bounded (PosN n b) where
    minBound = case sbinN :: SBinN b of
        SBE -> AtEnd (pure False)
        SB0 -> There0 minBound
        SB1 -> Here (pure False)

    maxBound = case sbinN :: SBinN b of
        SBE -> AtEnd (pure True)
        SB0 -> There0 maxBound
        SB1 -> There1 maxBound

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

explicitShow :: Pos b -> String
explicitShow b = explicitShowsPrec 0 b ""

explicitShowN :: PosN n b -> String
explicitShowN b = explicitShowsPrecN 0 b ""

explicitShowsPrec :: Int -> Pos b ->ShowS
explicitShowsPrec d (Pos b)
    = showParen (d > 10)
    $ showString "Pos "
    . explicitShowsPrecN 11 b

explicitShowsPrecN :: Int -> PosN n b ->ShowS
explicitShowsPrecN d (AtEnd v)
    = showParen (d > 10)
    $ showString "AtEnd "
    . showsPrec 11 v
explicitShowsPrecN d (Here v)
    = showParen (d > 10)
    $ showString "Here "
    . showsPrec 11 v
explicitShowsPrecN d (There1 p)
    = showParen (d > 10)
    $ showString "There1 "
    . explicitShowsPrecN 11 p
explicitShowsPrecN d (There0 p)
    = showParen (d > 10)
    $ showString "There0 "
    . explicitShowsPrecN 11 p

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert 'Pos' to 'Natural'
--
-- >>> fmap toNatural [minBound, maxBound :: Pos Bin7]
-- [0,6]
toNatural :: Pos b -> Natural
toNatural (Pos p) = toNaturalN p

-- | Convert 'PosN' to 'Natural'.
toNaturalN :: forall n b. N.SNatI n => PosN n b -> Natural
toNaturalN (AtEnd v)  = toNaturalV v
toNaturalN (Here v)   = toNaturalV v
toNaturalN (There1 p) = getKNat (exp2 :: KNat Natural n) + toNaturalN p
toNaturalN (There0 p) = toNaturalN p

exp2 :: N.SNatI n => KNat Natural n
exp2 = N.induction (KNat 1) (\(KNat n) -> KNat (n * 2))

toNaturalV :: Vec n Bool -> Natural
toNaturalV = foldl (\n b -> 2 * n + if b then 1 else 0) 0

-------------------------------------------------------------------------------
-- Interesting
-------------------------------------------------------------------------------

-- | @'Pos' 'BZ'@ is not inhabited.
absurd  :: Pos 'BZ -> b
absurd x = case x of {}

-- | Counting to one is boring
--
-- >>> boring
-- 0
boring :: Pos ('BN 'BE)
boring = minBound

-------------------------------------------------------------------------------
-- min and max, tricky, we need Pred.
-------------------------------------------------------------------------------

-- TBW

-------------------------------------------------------------------------------
-- top & pop
-------------------------------------------------------------------------------

-- | 'top' and 'pop' serve as 'FZ' and 'FS', with types specified so
-- type-inference works backwards from the result.
--
-- >>> top :: Pos Bin4
-- 0
--
-- >>> pop (pop top) :: Pos Bin4
-- 2
--
-- >>> pop (pop top) :: Pos Bin9
-- 2
--
top :: SBinNI b => Pos ('BN b)
top = minBound

-- | See 'top'.
pop :: Pop a b => Pos ('BN a) -> Pos ('BN b)
pop (Pos n) = Pos (pop' n)

-- | Class implmenenting 'pop'.
class Pop a b | b -> a where
    pop' :: PosN n a -> PosN n b

instance SBinNI b => Pop ('B0 b) ('B1 b) where
    pop' = weakenRight1N

instance Pop0 a b => Pop a ('B0 b) where
    pop' = pop0

class Pop0 a b | b -> a where
    pop0 :: PosN n a -> PosN n ('B0 b)

instance Pop0 'BE 'BE where
    pop0 = weakenRight1N

instance SBinNI b => Pop0 ('B1 ('B0 b)) ('B1 b) where
    pop0 = weakenRight1N

instance (SBinNI b, Pop0 a b) => Pop0 ('B1 a) ('B0 b) where
    pop0 (There1 p) = There0 (pop0 p)
    pop0 (Here v)   = There0 (weakenRight1V (True ::: v))

-------------------------------------------------------------------------------
-- Append and Split
-------------------------------------------------------------------------------

-- | Like 'FS' for 'Fin'.
--
-- Some tests:
--
-- >>> fmap weakenRight1 $ toList $ (universe :: RAL Bin2 (Pos Bin2))
-- [1,2]
--
-- >>> fmap weakenRight1 $ toList $ (universe :: RAL Bin3 (Pos Bin3))
-- [1,2,3]
--
-- >>> fmap weakenRight1 $ toList $ (universe :: RAL Bin4 (Pos Bin4))
-- [1,2,3,4]
--
-- >>> fmap weakenRight1 $ toList $ (universe :: RAL Bin5 (Pos Bin5))
-- [1,2,3,4,5]
--
-- >>> fmap weakenRight1 $ toList $ (universe :: RAL Bin6 (Pos Bin6))
-- [1,2,3,4,5,6]
--
weakenRight1 :: SBinNI b => Pos ('BN b) -> Pos (SuccN b)
weakenRight1 (Pos b) = Pos (weakenRight1N b)

weakenRight1N :: forall b n. SBinNI b => PosN n b -> PosN n (SuccN' b)
weakenRight1N = weakenRight1N' sbinN

weakenRight1N' :: forall b n. SBinN b -> PosN n b -> PosN n (SuccN' b)
weakenRight1N' SBE (AtEnd v)  = There0 (AtEnd (True ::: v)) -- weakenRight1V v))
weakenRight1N' SB0 (There0 p) = There1 p
weakenRight1N' SB1 (There1 p) = There0 (weakenRight1N' sbinN p)
weakenRight1N' s@SB1 (Here v) = There0 $ recur s v where
    recur :: forall bb. SBinNI bb => SBinN ('B1 bb) -> Vec n Bool -> PosN ('S n) (SuccN' bb)
    recur _ v' = withSuccN (Proxy :: Proxy bb) $ weakenRight1V (True ::: v')

weakenRight1V :: forall b n. SBinNI b => Vec ('S n) Bool -> PosN ('S n) b
weakenRight1V v = case sbinN :: SBinN b of
    SBE -> AtEnd v
    SB0 -> There0 (weakenRight1V (False ::: v))
    SB1 -> Here v

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

newtype KNat a (n :: Nat) = KNat { getKNat :: a }
