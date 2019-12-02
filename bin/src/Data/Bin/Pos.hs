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
module Data.Bin.Pos (
    Pos (..), PosP,
    -- * Top & Pop
    top, pop, Pop,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    -- * Conversions
    toNatural,
    -- * Interesting
    absurd,
    boring,
    -- * Weakening (succ)
    weakenRight1,
    -- * Universe
    universe,
    ) where

import Prelude
       (Bounded (..), Eq, Int, Integer, Ord (..), Show (..), ShowS, String,
       fmap, fromIntegral, map, showParen, showString, ($), (.))

import Data.Bin        (Bin (..), BinP (..))
import Data.BinP.PosP  (PosP (..), PosP' (..))
import Data.Nat        (Nat (..))
import Data.Typeable   (Typeable)
import Data.Wrd        (Wrd (..))
import Numeric.Natural (Natural)

import qualified Data.BinP.PosP  as PP
import qualified Data.Type.Bin   as B
import qualified Test.QuickCheck as QC

import Data.Type.Bin

-- $setup
-- >>> import Prelude (map, putStrLn)
-- >>> import Data.Foldable (traverse_)

-------------------------------------------------------------------------------
-- Data
-------------------------------------------------------------------------------

-- | 'Pos' is to 'Bin' is what 'Fin' is to 'Nat'.
--
-- The name is picked, as sthe lack of beter alternatives.
--
data Pos (b :: Bin) where
    Pos :: PosP b -> Pos ('BP b)
  deriving (Typeable)

deriving instance Eq (Pos b)
deriving instance Ord (Pos b)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (Pos b) where
    showsPrec d = showsPrec d . toNatural

-- |
--
-- >>> minBound < (maxBound :: Pos Bin5)
-- True
instance (SBinPI n, b ~ 'BP n) => Bounded (Pos b) where
    minBound = Pos minBound
    maxBound = Pos maxBound

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance (SBinPI n, b ~ 'BP n) => QC.Arbitrary (Pos b) where
    arbitrary = fmap Pos QC.arbitrary

instance QC.CoArbitrary (Pos b) where
    coarbitrary = QC.coarbitrary . (fromIntegral :: Natural -> Integer) . toNatural

instance (SBinPI n, b ~ 'BP n) => QC.Function (Pos b) where
    function = QC.functionMap (\(Pos p) -> p) Pos

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

explicitShow :: Pos b -> String
explicitShow b = explicitShowsPrec 0 b ""

explicitShowsPrec :: Int -> Pos b ->ShowS
explicitShowsPrec d (Pos b)
    = showParen (d > 10)
    $ showString "Pos "
    . PP.explicitShowsPrec 11 b

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert 'Pos' to 'Natural'
--
-- >>> map toNatural (universe :: [Pos Bin7])
-- [0,1,2,3,4,5,6]
toNatural :: Pos b -> Natural
toNatural (Pos p) = PP.toNatural p

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
boring :: Pos ('BP 'BE)
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
top :: SBinPI b => Pos ('BP b)
top = minBound

-- | See 'top'.
pop :: Pop a b => Pos ('BP a) -> Pos ('BP b)
pop (Pos (PosP n)) = Pos (PosP (pop' n))

-- | Class implmenenting 'pop'.
class Pop a b | b -> a where
    pop' :: PosP' n a -> PosP' n b

instance SBinPI b => Pop ('B0 b) ('B1 b) where
    pop' = PP.weakenRight1' sbinp

instance Pop0 a b => Pop a ('B0 b) where
    pop' = pop0

class Pop0 a b | b -> a where
    pop0 :: PosP' n a -> PosP' n ('B0 b)

instance Pop0 'BE 'BE where
    pop0 (AtEnd n) = There0 (AtEnd (W1 n))

instance SBinPI b => Pop0 ('B1 ('B0 b)) ('B1 b) where
    pop0 (Here v)            = There0 (Here (W1 v))
    pop0 (There1 (There0 p)) = There0 (There1 p)

instance (SBinPI b, Pop0 a b) => Pop0 ('B1 a) ('B0 b) where
    pop0 (There1 p) = There0 (pop0 p)
    pop0 (Here v)   = There0 (weakenRight1V (W1 v))

weakenRight1V :: forall b n. SBinPI b => Wrd ('S n) -> PosP' ('S n) b
weakenRight1V v = case sbinp :: SBinP b of
    SBE -> AtEnd v
    SB0 -> There0 (weakenRight1V (W0 v))
    SB1 -> Here v

-------------------------------------------------------------------------------
-- Append and Split
-------------------------------------------------------------------------------

-- | Like 'FS' for 'Fin'.
--
-- Some tests:
--
-- >>> map weakenRight1 $ (universe :: [Pos Bin2])
-- [1,2]
--
-- >>> map weakenRight1 $ (universe :: [Pos Bin3])
-- [1,2,3]
--
-- >>> map weakenRight1 $ (universe :: [Pos Bin4])
-- [1,2,3,4]
--
-- >>> map weakenRight1 $ (universe :: [Pos Bin5])
-- [1,2,3,4,5]
--
-- >>> map weakenRight1 $ (universe :: [Pos Bin6])
-- [1,2,3,4,5,6]
--
weakenRight1 :: SBinPI b => Pos ('BP b) -> Pos (Succ'' b)
weakenRight1 (Pos b) = Pos (PP.weakenRight1 b)

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- | Universe, i.e. all @[Pos b]@
--
-- >>> universe :: [Pos Bin9]
-- [0,1,2,3,4,5,6,7,8]
--
-- >>> traverse_ (putStrLn . explicitShow) (universe :: [Pos Bin5])
-- Pos (PosP (Here WE))
-- Pos (PosP (There1 (There0 (AtEnd 0b00))))
-- Pos (PosP (There1 (There0 (AtEnd 0b01))))
-- Pos (PosP (There1 (There0 (AtEnd 0b10))))
-- Pos (PosP (There1 (There0 (AtEnd 0b11))))
--
universe :: forall b. B.SBinI b => [Pos b]
universe = case B.sbin :: SBin b of
    B.SBZ -> []
    B.SBP -> map Pos PP.universe
