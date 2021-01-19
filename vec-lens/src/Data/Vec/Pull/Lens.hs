{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Vec.Pull.Lens (
    -- * Indexing
    ix,
    _Cons,
    _head,
    _tail,
    -- * Conversions
    _Vec,
    ) where

import Control.Lens ((<&>))
import Data.Fin     (Fin (..))
import Data.Nat     (Nat (..))

import qualified Control.Lens  as L
import qualified Data.Type.Nat as N

import Data.Vec.Pull

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Vec.Pull
-- >>> import Data.Fin (Fin (..))
-- >>> import Control.Lens ((^.), (&), (.~), over)
-- >>> import qualified Data.Vec.Lazy as L
-- >>> import qualified Data.Vec.Lazy.Lens as L

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) ^. L._Pull . ix (FS FZ)
-- 'b'
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) & L._Pull . ix (FS FZ) .~ 'x'
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: Fin n -> L.Lens' (Vec n a) a
ix i f (Vec v) = f (v i) <&> \a -> Vec $ \j ->
    if i == j
    then a
    else v j

-- | Match on non-empty 'Vec'.
--
-- /Note:/ @lens@ 'L._Cons' is a 'L.Prism'.
-- In fact, @'Vec' n a@ cannot have an instance of 'L.Cons' as types don't match.
--
_Cons :: L.Iso (Vec ('S n) a) (Vec ('S n) b) (a, Vec n a) (b, Vec n b)
_Cons = L.iso (\(Vec v) -> (v FZ, Vec (v . FS))) (\(x, xs) -> cons x xs)

-- | Head lens. /Note:/ @lens@ 'L._head' is a 'L.Traversal''.
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) ^. L._Pull . _head
-- 'a'
--
-- >>> ('a' L.::: 'b' L.::: 'c' L.::: L.VNil) & L._Pull . _head .~ 'x'
-- 'x' ::: 'b' ::: 'c' ::: VNil
--
_head :: L.Lens' (Vec ('S n) a) a
_head f (Vec v) = f (v FZ) <&> \a -> Vec $ \j -> case j of
    FZ -> a
    _   -> v j
{-# INLINE _head #-}

-- | Head lens. /Note:/ @lens@ 'L._head' is a 'L.Traversal''.
_tail :: L.Lens' (Vec ('S n) a) (Vec n a)
_tail f (Vec v) = f (Vec (v . FS)) <&> \xs -> cons (v FZ) xs
{-# INLINE _tail #-}

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Prism from list.
_Vec :: N.SNatI n => L.Prism' [a] (Vec n a)
_Vec = L.prism' toList fromList

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if !MIN_VERSION_lens(5,0,0)
instance L.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

instance N.SNatI n => L.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr
#endif
