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
module Data.BinP.PosP (
    PosP (..),
    PosP' (..),
    -- * Top & Pop
    top, pop,
    -- * Showing
    explicitShow,
    explicitShow',
    explicitShowsPrec,
    explicitShowsPrec',
    -- * Conversions
    toNatural, toNatural',
    -- * Interesting
    boring,
    -- * Weakening (succ)
    weakenRight1, weakenRight1',
    -- * Universe
    universe, universe',
    ) where

import Prelude
       (Bounded (..), Either (..), Eq, Int, Integer, Num, Ord (..),
       Ordering (..), Show (..), ShowS, String, either, fmap, fromIntegral, map,
       showParen, showString, ($), (*), (+), (++), (.))

import Control.DeepSeq (NFData (..))
import Data.Bin        (BinP (..))
import Data.Nat        (Nat (..))
import Data.Proxy      (Proxy (..))
import Data.Typeable   (Typeable)
import Data.Wrd        (Wrd (..))
import Numeric.Natural (Natural)

import qualified Data.Bin        as B
import qualified Data.Boring     as Boring
import qualified Data.Type.Bin   as B
import qualified Data.Type.BinP  as BP
import qualified Data.Type.Nat   as N
import qualified Data.Wrd        as W
import qualified Test.QuickCheck as QC

import Data.Type.BinP

-- $setup
-- >>> import Prelude (map, putStrLn)
-- >>> import Data.Foldable (traverse_)
-- >>> import qualified Data.Type.Nat as N
-- >>> import Data.Type.BinP

-------------------------------------------------------------------------------
-- Data
-------------------------------------------------------------------------------

-- | 'PosP' is to 'BinP' is what 'Fin' is to 'Nat', when 'n' is 'Z'.
newtype PosP (b :: BinP) = PosP { unPosP :: PosP' 'Z b }
  deriving (Eq, Ord, Typeable)

-- | 'PosP'' is a structure inside 'PosP'.
data PosP' (n :: Nat) (b :: BinP) where
    AtEnd  :: Wrd n          -> PosP' n 'BE      -- ^ position is either at the last digit;
    Here   :: Wrd n          -> PosP' n ('B1 b)  -- ^ somewhere here
    There1 :: PosP' ('S n) b -> PosP' n ('B1 b)  -- ^ or there, if the bit is one;
    There0 :: PosP' ('S n) b -> PosP' n ('B0 b)  -- ^ or only there if it is none.
  deriving (Typeable)

deriving instance Eq (PosP' n b)
instance Ord (PosP' n b) where
    compare (AtEnd  x) (AtEnd  y) = compare x y
    compare (Here   x) (Here   y) = compare x y
    compare (Here   _) (There1 _) = LT
    compare (There1 _) (Here   _) = GT
    compare (There1 x) (There1 y) = compare x y
    compare (There0 x) (There0 y) = compare x y

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (PosP b) where
    showsPrec d = showsPrec d . toNatural

instance N.SNatI n => Show (PosP' n b) where
    showsPrec d = showsPrec d . toNatural'

instance SBinPI b => Bounded (PosP b) where
    minBound = PosP minBound
    maxBound = PosP maxBound

instance (N.SNatI n, SBinPI b) => Bounded (PosP' n b) where
    minBound = case sbinp :: SBinP b of
        SBE -> AtEnd minBound
        SB0 -> There0 minBound
        SB1 -> Here minBound

    maxBound = case sbinp :: SBinP b of
        SBE -> AtEnd maxBound
        SB0 -> There0 maxBound
        SB1 -> There1 maxBound

-- | @since 0.1.2
instance NFData (PosP b) where
    rnf (PosP p) = rnf p

-- | @since 0.1.2
instance NFData (PosP' n b) where
    rnf (AtEnd w)  = rnf w
    rnf (Here w)   = rnf w
    rnf (There1 p) = rnf p
    rnf (There0 p) = rnf p

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance SBinPI b => QC.Arbitrary (PosP b) where
    arbitrary = fmap PosP QC.arbitrary

instance QC.CoArbitrary (PosP b) where
    coarbitrary = QC.coarbitrary . (fromIntegral :: Natural -> Integer) . toNatural

instance SBinPI b => QC.Function (PosP b) where
    function = QC.functionMap (\(PosP p) -> p) PosP

instance (N.SNatI n, SBinPI b) => QC.Arbitrary (PosP' n b) where
    arbitrary = case sbinp :: SBinP b of
        SBE -> fmap AtEnd QC.arbitrary
        SB0 -> fmap There0 QC.arbitrary
        SB1 -> sb1freq
      where
        sb1freq :: forall bb. SBinPI bb => QC.Gen (PosP' n ('B1 bb))
        sb1freq = QC.frequency
            [ (fHere,  fmap Here QC.arbitrary)
            , (fThere, fmap There1 QC.arbitrary)
            ]
          where
            fHere  = getKNat (exp2 :: KNat Int n)
            fThere = fHere * 2 * BP.reflectToNum (Proxy :: Proxy bb)

instance N.SNatI n => QC.CoArbitrary (PosP' n b) where
    coarbitrary = QC.coarbitrary . (fromIntegral :: Natural -> Integer) . toNatural'

instance (N.SNatI n, SBinPI b) => QC.Function (PosP' n b) where
    function = case sbinp :: SBinP b of
        SBE -> QC.functionMap (\(AtEnd t)  -> t) AtEnd
        SB0 -> QC.functionMap (\(There0 r) -> r) There0
        SB1 -> QC.functionMap sp (either Here There1) where
      where
        sp :: PosP' n ('B1 bb) -> Either (Wrd n) (PosP' ('S n) bb)
        sp (Here t)   = Left t
        sp (There1 p) = Right p

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

explicitShow :: PosP b -> String
explicitShow b = explicitShowsPrec 0 b ""

explicitShow' :: PosP' n b -> String
explicitShow' b = explicitShowsPrec' 0 b ""

explicitShowsPrec :: Int -> PosP b ->ShowS
explicitShowsPrec d (PosP p)
    = showParen (d > 10)
    $ showString "PosP "
    . explicitShowsPrec' 11 p

explicitShowsPrec' :: Int -> PosP' n b ->ShowS
explicitShowsPrec' d (AtEnd v)
    = showParen (d > 10)
    $ showString "AtEnd "
    . showsPrec 11 v
explicitShowsPrec' d (Here v)
    = showParen (d > 10)
    $ showString "Here "
    . showsPrec 11 v
explicitShowsPrec' d (There1 p)
    = showParen (d > 10)
    $ showString "There1 "
    . explicitShowsPrec' 11 p
explicitShowsPrec' d (There0 p)
    = showParen (d > 10)
    $ showString "There0 "
    . explicitShowsPrec' 11 p

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Convert 'PosP' to 'Natural'.
toNatural :: PosP b -> Natural
toNatural (PosP p) = toNatural' p

-- | Convert 'PosP'' to 'Natural'.
toNatural' :: forall n b. N.SNatI n => PosP' n b -> Natural
toNatural' (AtEnd v)  = W.toNatural v
toNatural' (Here v)   = W.toNatural v
toNatural' (There1 p) = getKNat (exp2 :: KNat Natural n) + toNatural' p
toNatural' (There0 p) = toNatural' p

exp2 :: Num a => N.SNatI n => KNat a n
exp2 = N.induction (KNat 1) (\(KNat n) -> KNat (n * 2))

-------------------------------------------------------------------------------
-- Interesting
-------------------------------------------------------------------------------

-- | Counting to one is boring
--
-- >>> boring
-- 0
boring :: PosP 'BE
boring = minBound

-------------------------------------------------------------------------------
-- top & pop
-------------------------------------------------------------------------------

-- | 'top' and 'pop' serve as 'FZ' and 'FS', with types specified so
-- type-inference works backwards from the result.
--
-- >>> top :: PosP BinP4
-- 0
--
-- >>> pop (pop top) :: PosP BinP4
-- 2
--
-- >>> pop (pop top) :: PosP BinP9
-- 2
--
top :: SBinPI b => PosP b
top = minBound

-- | See 'top'.
pop :: (SBinPI a, B.Pred b ~ 'B.BP a, Succ a ~ b) => PosP a -> PosP b
pop = weakenRight1

-------------------------------------------------------------------------------
-- Append and Split
-------------------------------------------------------------------------------

weakenRight1 :: SBinPI b => PosP b -> PosP (Succ b)
weakenRight1 (PosP n) = PosP (weakenRight1' sbinp n)

weakenRight1' :: forall b n. SBinP b -> PosP' n b -> PosP' n (Succ b)
weakenRight1' SBE (AtEnd v)  = There0 (AtEnd (W1 v))
weakenRight1' SB0 (There0 p) = There1 p
weakenRight1' SB1 (There1 p) = There0 (weakenRight1' sbinp p)
weakenRight1' s@SB1 (Here v) = There0 $ recur s v where
    recur :: forall bb. SBinPI bb => SBinP ('B1 bb) -> Wrd n -> PosP' ('S n) (Succ bb)
    recur _ v' = withSucc (Proxy :: Proxy bb) $ weakenRight1V (W1 v')

weakenRight1V :: forall b n. SBinPI b => Wrd ('S n) -> PosP' ('S n) b
weakenRight1V v = case sbinp :: SBinP b of
    SBE -> AtEnd v
    SB0 -> There0 (weakenRight1V (W0 v))
    SB1 -> Here v

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------

-- |
--
-- >>> universe :: [PosP BinP9]
-- [0,1,2,3,4,5,6,7,8]
--
universe :: forall b. SBinPI b => [PosP b]
universe = map PosP universe'

-- | This gives a hint, what the @n@ parameter means in 'PosP''.
--
-- >>> universe' :: [PosP' N.Nat2 BinP2]
-- [0,1,2,3,4,5,6,7]
--
universe' :: forall b n. (N.SNatI n, SBinPI b) => [PosP' n b]
universe' = case B.sbinp :: SBinP b of
    B.SBE -> map AtEnd W.universe
    B.SB0 -> map There0 universe'
    B.SB1 -> map Here W.universe ++ map There1 universe'

-------------------------------------------------------------------------------
-- Boring
-------------------------------------------------------------------------------

-- | @since 0.1.2
instance b ~ 'BE => Boring.Boring (PosP b) where
    boring = boring

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

newtype KNat a (n :: Nat) = KNat { getKNat :: a }
