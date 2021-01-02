{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Vec.Lazy.Inline.Lens (
    -- * Indexing
    ix,
    _Cons,
    _head,
    _tail,
    -- * Conversions
    _Pull,
    _Vec,
    ) where

import Data.Fin           (Fin (..))
import Data.Nat           (Nat (..))
import Data.Vec.Lazy.Lens (_Cons, _head, _tail)
import Prelude            (Functor, ($), (.))

import qualified Control.Lens  as L
import qualified Data.Fin      as F
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P

import Data.Vec.Lazy.Inline

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Prelude (Maybe (..), Char, Bool (..))
-- >>> import Control.Lens ((^.), (&), (.~), over, (^?), (#))

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) ^. ix (FS FZ)
-- 'b'
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) & ix (FS FZ) .~ 'x'
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: forall n f a. (N.SNatI n, Functor f) => Fin n -> L.LensLike' f (Vec n a) a
ix = getIxLens $ N.induction1 start step where
    start :: IxLens f 'Z a
    start = IxLens F.absurd

    step :: IxLens f m a -> IxLens f ('S m) a
    step (IxLens l) = IxLens $ \i -> case i of
        FZ   -> _head
        FS j -> _tail . l j

newtype IxLens f n a = IxLens { getIxLens :: Fin n -> L.LensLike' f (Vec n a) a }

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | An 'L.Iso' from 'toPull' and 'fromPull'.
_Pull :: N.SNatI n => L.Iso (Vec n a) (Vec n b) (P.Vec n a) (P.Vec n b)
_Pull = L.iso toPull fromPull

-- | Prism from list.
--
-- >>> "foo" ^? _Vec :: Maybe (Vec N.Nat3 Char)
-- Just ('f' ::: 'o' ::: 'o' ::: VNil)
--
-- >>> "foo" ^? _Vec :: Maybe (Vec N.Nat2 Char)
-- Nothing
--
-- >>> _Vec # (True ::: False ::: VNil)
-- [True,False]
--
_Vec :: N.SNatI n => L.Prism' [a] (Vec n a)
_Vec = L.prism' toList fromList
