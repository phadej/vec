{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Vec.Lazy.Inline.Optics (
    -- * Indexing
    ix,
    _Cons,
    _head,
    _tail,
    -- * Conversions
    _Pull,
    _Vec,
    ) where

import Control.Applicative  ((<$>))
import Data.Fin             (Fin (..))
import Data.Nat             (Nat (..))
import Data.Vec.Lazy.Optics (_Cons, _head, _tail)
import Prelude              (Functor, ($), (.))

import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P
import qualified Optics.Core   as L

import Data.Vec.Lazy.Inline

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Fin (Fin (..))
-- >>> import Data.Vec.Lazy.Inline
-- >>> import Prelude (Maybe (..), Char, Bool (..))
-- >>> import Optics.Core (over, view, set, (%), review, preview)

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> view (ix (FS FZ)) ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'b'
--
-- >>> set (ix (FS FZ)) 'x' ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: forall n a. N.SNatI n => Fin n -> L.Lens' (Vec n a) a
ix i = L.lensVL (ixVL i)
{-# INLINE ix #-}

ixVL :: forall n f a. (N.SNatI n, Functor f) => Fin n -> LensLikeVL' f (Vec n a) a
ixVL = getIxLens $ N.induction1 start step where
    start :: IxLens f 'Z a
    start = IxLens F.absurd

    step :: IxLens f m a -> IxLens f ('S m) a
    step (IxLens l) = IxLens $ \i -> case i of
        FZ   -> headVL
        FS j -> tailVL . l j
{-# INLINE ixVL #-}

newtype IxLens f n a = IxLens { getIxLens :: Fin n -> LensLikeVL' f (Vec n a) a }

headVL :: Functor f => LensLikeVL' f (Vec ('S n) a) a
headVL f (x ::: xs) = (::: xs) <$> f x
{-# INLINE headVL #-}

tailVL :: Functor f => LensLikeVL' f (Vec ('S n) a) (Vec n a)
tailVL f (x ::: xs) = (x :::) <$> f xs
{-# INLINE tailVL #-}

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | An 'L.Iso' from 'toPull' and 'fromPull'.
_Pull :: N.SNatI n => L.Iso (Vec n a) (Vec n b) (P.Vec n a) (P.Vec n b)
_Pull = L.iso toPull fromPull

-- | Prism from list.
--
-- >>> preview _Vec "foo" :: Maybe (Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> preview _Vec "foo" :: Maybe (Vec N.Nat2 Char)
-- Nothing
--
-- >>> review _Vec (True ::: False ::: VNil)
-- [True,False]
--
_Vec :: N.SNatI n => L.Prism' [a] (Vec n a)
_Vec = L.prism' toList fromList
