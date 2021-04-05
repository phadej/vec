{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE Safe                   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
module Data.Bin.Pos (
    Pos (..), PosP,
    -- * Top & Pop
    top, pop,
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
import Data.BinP.PosP  (PosP (..))
import Data.Typeable   (Typeable)
import Numeric.Natural (Natural)

import qualified Data.BinP.PosP  as PP
import qualified Data.Boring     as Boring
import qualified Data.Type.Bin   as B
import qualified Data.Type.BinP  as BP
import qualified Test.QuickCheck as QC

import Data.Type.Bin

-- $setup
-- >>> import Prelude (map, putStrLn, Ord (..), Bounded (..), ($), (.))
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Type.Bin

-------------------------------------------------------------------------------
-- Data
-------------------------------------------------------------------------------

-- | 'Pos' is to 'Bin' is what 'Fin' is to 'Nat'.
--
-- The name is picked, as the lack of better alternatives.
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
pop :: (SBinPI a, Pred b ~ 'BP a, BP.Succ a ~ b) => Pos ('BP a) -> Pos ('BP b)
pop = weakenRight1

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
-- Boring
-------------------------------------------------------------------------------

-- | @since 0.1.2
instance b ~ 'BP 'BE => Boring.Boring (Pos b) where
    boring = boring

-- | @since 0.1.2
instance b ~ 'BZ => Boring.Absurd (Pos b) where
    absurd = absurd

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
