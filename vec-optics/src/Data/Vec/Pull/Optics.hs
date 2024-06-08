{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Vec.Pull.Optics (
    -- * Indexing
    ix,
    _Cons,
    _head,
    _tail,
    -- * Conversions
    _Vec,
    ) where

import Data.Fin    (Fin (..))
import Data.Nat    (Nat (..))
import Optics.Core ((<&>))

import qualified Data.Type.Nat as N
import qualified Optics.Core   as L

import Data.Vec.Pull

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Fin (Fin (..))
-- >>> import Data.Vec.Pull
-- >>> import Optics.Core (over, view, set, (%))
-- >>> import qualified Data.Vec.Lazy as L
-- >>> import qualified Data.Vec.Lazy.Optics as L

type LensLikeVL f s t a b = (a -> f b) -> s -> f t
type LensLikeVL' f s a = LensLikeVL f s s a a

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- 'a' ::: 'x' ::: 'c' ::: VNil
-- >>> view (L._Pull % ix (FS FZ)) ('a' L.::: 'b' L.::: 'c' L.::: L.VNil)
-- 'b'
--
-- >>> set (L._Pull % ix (FS FZ)) 'x' ('a' L.::: 'b' L.::: 'c' L.::: L.VNil)
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: Fin n -> L.Lens' (Vec n a) a
ix i = L.lensVL (ixVL i)
{-# INLINE ix #-}

ixVL :: Functor f => Fin n -> LensLikeVL' f (Vec n a) a
ixVL i f (Vec v) = f (v i) <&> \a -> Vec $ \j ->
    if i == j
    then a
    else v j
{-# INLINE ixVL #-}

-- | Match on non-empty 'Vec'.
--
-- /Note:/ @lens@ 'L._Cons' is a 'L.Prism'.
-- In fact, @'Vec' n a@ cannot have an instance of 'L.Cons' as types don't match.
--
_Cons :: L.Iso (Vec ('S n) a) (Vec ('S n) b) (a, Vec n a) (b, Vec n b)
_Cons = L.iso (\(Vec v) -> (v FZ, Vec (v . FS))) (\(x, xs) -> cons x xs)

-- | Head lens. /Note:/ @lens@ 'L._head' is a 'L.Traversal''.
--
-- >>> view (L._Pull % _head) ('a' L.::: 'b' L.::: 'c' L.::: L.VNil)
-- 'a'
--
-- >>> set (L._Pull % _head) 'x' ('a' L.::: 'b' L.::: 'c' L.::: L.VNil)
-- 'x' ::: 'b' ::: 'c' ::: VNil
--
_head :: L.Lens' (Vec ('S n) a) a
_head = L.lensVL headVL
{-# INLINE _head #-}

headVL :: Functor f => LensLikeVL' f (Vec ('S n) a) a
headVL f (Vec v) = f (v FZ) <&> \a -> Vec $ \j -> case j of
    FZ -> a
    _   -> v j
{-# INLINE headVL #-}

-- | Tail lens.
_tail :: L.Lens' (Vec ('S n) a) (Vec n a)
_tail = L.lensVL tailVL
{-# INLINE _tail #-}

tailVL :: Functor f => LensLikeVL' f (Vec ('S n) a) (Vec n a)
tailVL f (Vec v) = f (Vec (v . FS)) <&> \xs -> cons (v FZ) xs
{-# INLINE tailVL #-}

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Prism from list.
_Vec :: N.SNatI n => L.Prism' [a] (Vec n a)
_Vec = L.prism' toList fromList
