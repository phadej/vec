{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Vec.Lazy.Optics  (
    -- * Indexing
    ix,
    _Cons,
    _head,
    _tail,
    -- * Conversions
    _Pull,
    _Vec,
    ) where

import Control.Applicative ((<$>))
import Data.Fin            (Fin (..))
import Data.Nat            (Nat (..))
import Prelude             ((.), Functor, ($))

import qualified Optics.Core  as L
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P

import Data.Vec.Lazy

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Fin (Fin (..))
-- >>> import Data.Vec.Lazy
-- >>> import Prelude (Maybe (..), Char, Bool (..))
-- >>> import Optics.Core (over, view, set, (%), review, preview)
-- >>> import qualified Data.Type.Nat as N

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
ix :: Fin n -> L.Lens' (Vec n a) a
ix i = L.lensVL (ixVL i)
{-# INLINE ix #-}

ixVL :: Functor f => Fin n -> LensLikeVL' f (Vec n a) a
ixVL FZ     f (x ::: xs) = (::: xs) <$> f x
ixVL (FS n) f (x ::: xs) = (x :::)  <$> ixVL n f xs

-- | Match on non-empty 'Vec'.
--
-- /Note:/ @lens@ 'L._Cons' is a 'L.Prism'.
-- In fact, @'Vec' n a@ cannot have an instance of 'L.Cons' as types don't match.
--
_Cons :: L.Iso (Vec ('S n) a) (Vec ('S n) b) (a, Vec n a) (b, Vec n b)
_Cons = L.iso (\(x ::: xs) -> (x, xs)) (\(x, xs) -> x ::: xs)

-- | Head lens. /Note:/ @lens@ 'L._head' is a 'L.Traversal''.
--
-- >>> view _head ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'a'
--
-- >>> set _head 'x' ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'x' ::: 'b' ::: 'c' ::: VNil
--
_head :: L.Lens' (Vec ('S n) a) a
_head = L.lensVL headVL
{-# INLINE _head #-}

headVL :: Functor f => LensLikeVL' f (Vec ('S n) a) a
headVL f (x ::: xs) = (::: xs) <$> f x
{-# INLINE headVL #-}

-- | Tail lens.
_tail :: L.Lens' (Vec ('S n) a) (Vec n a)
_tail = L.lensVL tailVL
{-# INLINE _tail #-}

tailVL :: Functor f => LensLikeVL' f (Vec ('S n) a) (Vec n a)
tailVL f (x ::: xs) = (x :::) <$> f xs
{-# INLINE tailVL #-}

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | An 'I.Iso' from 'toPull' and 'fromPull'.
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

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if !MIN_VERSION_optics_core(0,4,0)
instance L.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

instance L.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.TraversableWithIndex (Fin n) (Vec n) where
    itraverse = itraverse
#endif

instance L.Each (Fin n) (Vec n a) (Vec n b) a b where

type instance L.Index (Vec n a)   = Fin n
type instance L.IxValue (Vec n a) = a

-- | 'Vec' doesn't have 'L.At' instance, as we __cannot__ remove value from 'Vec'.
-- See 'ix' in "Data.Vec.Lazy" module for an 'L.Optics' (not 'L.Traversal').
instance L.Ixed (Vec n a) where
    type IxKind (Vec n a) = L.A_Lens
    ix = ix

instance L.Field1 (Vec ('S n) a) (Vec ('S n) a) a a where
    _1 = _head

instance L.Field2 (Vec ('S ('S n)) a) (Vec ('S ('S n)) a) a a where
    _2 = L.lensVL $ tailVL . headVL

instance L.Field3 (Vec ('S ('S ('S n))) a) (Vec ('S ('S ('S n))) a) a a where
    _3 = L.lensVL $ tailVL . tailVL . headVL

instance L.Field4 (Vec ('S ('S ('S ('S n)))) a) (Vec ('S ('S ('S ('S n)))) a) a a where
    _4 = L.lensVL $ tailVL . tailVL . tailVL . headVL

instance L.Field5 (Vec ('S ('S ('S ('S ('S n))))) a) (Vec ('S ('S ('S ('S ('S n))))) a) a a where
    _5 = L.lensVL $ tailVL . tailVL . tailVL . tailVL . headVL

instance L.Field6 (Vec ('S ('S ('S ('S ('S ('S n)))))) a) (Vec ('S ('S ('S ('S ('S ('S n)))))) a) a a where
    _6 = L.lensVL $ tailVL . tailVL . tailVL . tailVL . tailVL . headVL

instance L.Field7 (Vec ('S ('S ('S ('S ('S ('S ('S n))))))) a) (Vec ('S ('S ('S ('S ('S ('S ('S n))))))) a) a a where
    _7 = L.lensVL $ tailVL . tailVL . tailVL . tailVL . tailVL . tailVL . headVL

instance L.Field8 (Vec ('S ('S ('S ('S ('S ('S ('S ('S n)))))))) a) (Vec ('S ('S ('S ('S ('S ('S ('S ('S n)))))))) a) a a where
    _8 = L.lensVL $ tailVL . tailVL . tailVL . tailVL . tailVL . tailVL . tailVL . headVL

instance L.Field9 (Vec ('S ('S ('S ('S ('S ('S ('S ('S ('S n))))))))) a) (Vec ('S ('S ('S ('S ('S ('S ('S ('S ('S n))))))))) a) a a where
    _9 = L.lensVL $ tailVL . tailVL . tailVL . tailVL . tailVL . tailVL . tailVL . tailVL . headVL
