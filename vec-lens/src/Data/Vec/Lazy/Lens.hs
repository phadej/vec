{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Vec.Lazy.Lens  (
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
import Prelude             ((.))

import qualified Control.Lens  as L
import qualified Data.Type.Nat as N
import qualified Data.Vec.Pull as P

import Data.Vec.Lazy

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Vec.Lazy
-- >>> import Data.Fin (Fin (..))
-- >>> import Prelude (Maybe (..), Char, Bool (..))
-- >>> import Control.Lens ((^.), (&), (.~), over, (^?), (#))
-- >>> import qualified Data.Type.Nat as N

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
ix :: Fin n -> L.Lens' (Vec n a) a
ix FZ     f (x ::: xs) = (::: xs) <$> f x
ix (FS n) f (x ::: xs) = (x :::)  <$> ix n f xs

-- | Match on non-empty 'Vec'.
--
-- /Note:/ @lens@ 'L._Cons' is a 'L.Prism'.
-- In fact, @'Vec' n a@ cannot have an instance of 'L.Cons' as types don't match.
--
_Cons :: L.Iso (Vec ('S n) a) (Vec ('S n) b) (a, Vec n a) (b, Vec n b)
_Cons = L.iso (\(x ::: xs) -> (x, xs)) (\(x, xs) -> x ::: xs)

-- | Head lens. /Note:/ @lens@ 'L._head' is a 'L.Traversal''.
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) ^. _head
-- 'a'
--
-- >>> ('a' ::: 'b' ::: 'c' ::: VNil) & _head .~ 'x'
-- 'x' ::: 'b' ::: 'c' ::: VNil
--
_head :: L.Lens' (Vec ('S n) a) a
_head f (x ::: xs) = (::: xs) <$> f x
{-# INLINE _head #-}

-- | Tail lens.
_tail :: L.Lens' (Vec ('S n) a) (Vec n a)
_tail f (x ::: xs) = (x :::) <$> f xs
{-# INLINE _tail #-}

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | An 'I.Iso' from 'toPull' and 'fromPull'.
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

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

#if !MIN_VERSION_lens(5,0,0)
instance L.FunctorWithIndex (Fin n) (Vec n) where
    imap = imap

instance L.FoldableWithIndex (Fin n) (Vec n) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.TraversableWithIndex (Fin n) (Vec n) where
    itraverse = itraverse
#endif

instance L.Each (Vec n a) (Vec n b) a b where
    each = traverse

type instance L.Index (Vec n a)   = Fin n
type instance L.IxValue (Vec n a) = a

-- | 'Vec' doesn't have 'L.At' instance, as we __cannot__ remove value from 'Vec'.
-- See 'ix' in "Data.Vec.Lazy" module for an 'L.Lens' (not 'L.Traversal').
instance L.Ixed (Vec n a) where
    ix i = ix i

instance L.Field1 (Vec ('S n) a) (Vec ('S n) a) a a where
    _1 = _head

instance L.Field2 (Vec ('S ('S n)) a) (Vec ('S ('S n)) a) a a where
    _2 = _tail . _head

instance L.Field3 (Vec ('S ('S ('S n))) a) (Vec ('S ('S ('S n))) a) a a where
    _3 = _tail . _tail . _head

instance L.Field4 (Vec ('S ('S ('S ('S n)))) a) (Vec ('S ('S ('S ('S n)))) a) a a where
    _4 = _tail . _tail . _tail . _head

instance L.Field5 (Vec ('S ('S ('S ('S ('S n))))) a) (Vec ('S ('S ('S ('S ('S n))))) a) a a where
    _5 = _tail . _tail . _tail . _tail . _head

instance L.Field6 (Vec ('S ('S ('S ('S ('S ('S n)))))) a) (Vec ('S ('S ('S ('S ('S ('S n)))))) a) a a where
    _6 = _tail . _tail . _tail . _tail . _tail . _head

instance L.Field7 (Vec ('S ('S ('S ('S ('S ('S ('S n))))))) a) (Vec ('S ('S ('S ('S ('S ('S ('S n))))))) a) a a where
    _7 = _tail . _tail . _tail . _tail . _tail . _tail . _head

instance L.Field8 (Vec ('S ('S ('S ('S ('S ('S ('S ('S n)))))))) a) (Vec ('S ('S ('S ('S ('S ('S ('S ('S n)))))))) a) a a where
    _8 = _tail . _tail . _tail . _tail . _tail . _tail . _tail . _head

instance L.Field9 (Vec ('S ('S ('S ('S ('S ('S ('S ('S ('S n))))))))) a) (Vec ('S ('S ('S ('S ('S ('S ('S ('S ('S n))))))))) a) a a where
    _9 = _tail . _tail . _tail . _tail . _tail . _tail . _tail . _tail . _head
