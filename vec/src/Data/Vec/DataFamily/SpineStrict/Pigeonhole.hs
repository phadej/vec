{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Data.Vec.DataFamily.SpineStrict.Pigeonhole (
    Pigeonhole (..),
    -- * Representable
    gindex,
    gtabulate,
    gix,
    -- ** Traversable with index
    gtraverse,
    gitraverse,
    -- * Generic implementation
    gfrom, GFrom,
    gto, GTo,
    GPigeonholeSize,
    ) where

import Prelude (Functor (..), fst, uncurry, ($), (.))

import Control.Applicative             (Applicative (..), (<$>))
import Control.Arrow                   (first)
import Data.Fin                        (Fin (..))
import Data.Functor.Confusing          (confusing, fusing, iconfusing)
import Data.Functor.Identity           (Identity (..))
import Data.Functor.Product            (Product (..))
import Data.Nat                        (Nat (..))
import Data.Proxy                      (Proxy (..))
import Data.Vec.DataFamily.SpineStrict (Vec (..), tabulate)
import GHC.Generics                    ((:*:) (..), M1 (..), Par1 (..), U1 (..))

import qualified Control.Lens.Yocto              as Lens
import qualified Data.Fin                        as F
import qualified Data.Fin.Enum                   as F
import qualified Data.Type.Nat                   as N
import qualified Data.Vec.DataFamily.SpineStrict as V
import qualified GHC.Generics                    as G

#ifdef MIN_VERSION_transformers_compat
import Control.Monad.Trans.Instances ()
#endif

-- $setup
-- >>> :set -XDeriveGeneric
-- >>> import Control.Applicative (Const (..))
-- >>> import Data.Char (toUpper)
-- >>> import Data.Void (absurd)
-- >>> import GHC.Generics (Generic, Generic1)
-- >>> import Prelude (Int, Show, Char, Integer)

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Generic pigeonholes.
--
-- /Examples:/
--
-- >>> from (Identity 'a')
-- 'a' ::: VNil
--
-- >>> data Values a = Values a a a deriving (Generic1)
-- >>> instance Pigeonhole Values
-- >>> from (Values 1 2 3)
-- 1 ::: 2 ::: 3 ::: VNil
--
class Pigeonhole f where
    -- | The size of a pigeonhole
    type PigeonholeSize f :: Nat
    type PigeonholeSize f = GPigeonholeSize f

    -- | Converts a value to vector
    from :: f x -> Vec (PigeonholeSize f) x
    default from :: (G.Generic1 f, GFrom f, PigeonholeSize f ~ GPigeonholeSize f) => f x -> Vec (PigeonholeSize f) x
    from = gfrom

    -- | Converts back from vector.
    to :: Vec (PigeonholeSize f) x -> f x
    default to :: (G.Generic1 f, GTo f, PigeonholeSize f ~ GPigeonholeSize f) => Vec (PigeonholeSize f) x -> f x
    to = gto

-- | @'Identity' x@ ~ @x ^ 1@
instance Pigeonhole Identity
--
-- | @'Proxy' x@ ~ @x ^ 0@
instance Pigeonhole Proxy where
    type PigeonholeSize Proxy = 'Z
    from _ = VNil
    to _   = Proxy

-- | @'Product' f g x@ ~ @x ^ (size f + size g)@
instance (Pigeonhole f, Pigeonhole g, N.SNatI (PigeonholeSize f)) => Pigeonhole (Product f g) where
    type PigeonholeSize (Product f g) = N.Plus (PigeonholeSize f) (PigeonholeSize g)

    to = f . V.split where f (a, b) = Pair (to a) (to b)
    from = uncurry (V.++) . g where g (Pair a b) = (from a, from b)

-------------------------------------------------------------------------------
-- Generic representable
-------------------------------------------------------------------------------

-- | Index.
--
-- >>> gindex (Identity 'y') (Proxy :: Proxy Int)
-- 'y'
--
-- >>> data Key = Key1 | Key2 | Key3 deriving (Generic)
-- >>> data Values a = Values a a a deriving (Generic1)
--
-- >>> gindex (Values 'a' 'b' 'c') Key2
-- 'b'
--
gindex
    :: ( G.Generic i, F.GFrom i, G.Generic1 f, GFrom f
       , F.GEnumSize i ~ GPigeonholeSize f, N.SNatI (GPigeonholeSize f)
       )
     => f a -> i -> a
gindex fa i = gfrom fa V.! F.gfrom i

-- | Tabulate.
--
-- >>> gtabulate (\() -> 'x') :: Identity Char
-- Identity 'x'
--
-- >>> gtabulate absurd :: Proxy Integer
-- Proxy
--
-- >>> gtabulate absurd :: Proxy Integer
-- Proxy
--
gtabulate
    :: ( G.Generic i, F.GTo i, G.Generic1 f, GTo f
       , F.GEnumSize i ~ GPigeonholeSize f, N.SNatI (GPigeonholeSize f)
       )
     => (i -> a) -> f a
gtabulate idx = gto $ tabulate (idx . F.gto)

-- | A lens. @i -> Lens' (t a) a@
--
-- >>> Lens.view (gix ()) (Identity 'x')
-- 'x'
--
-- >>> Lens.over (gix ()) toUpper (Identity 'x')
-- Identity 'X'
--
gix :: ( G.Generic i, F.GFrom i, G.Generic1 t, GTo t, GFrom t
       , F.GEnumSize i ~ GPigeonholeSize t, N.SNatI (GPigeonholeSize t)
       , Functor f
       )
    => i -> (a -> f a) -> t a -> f (t a)
gix i = fusing $ \ab ta -> gto <$> ix (F.gfrom i) ab (gfrom ta)

-------------------------------------------------------------------------------
-- Vendored in ix
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> Lens.view (ix (FS FZ)) ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'b'
--
-- >>> Lens.set (ix (FS FZ)) 'x' ('a' ::: 'b' ::: 'c' ::: VNil)
-- 'a' ::: 'x' ::: 'c' ::: VNil
--
ix :: forall n f a. (N.SNatI n, Functor f) => Fin n -> Lens.LensLike' f (Vec n a) a
ix = getIxLens $ N.induction1 start step where
    start :: IxLens f 'Z a
    start = IxLens F.absurd

    step :: IxLens f m a -> IxLens f ('S m) a
    step (IxLens l) = IxLens $ \i -> case i of
        FZ   -> _head
        FS j -> _tail . l j

newtype IxLens f n a = IxLens { getIxLens :: Fin n -> Lens.LensLike' f (Vec n a) a }

_head :: Lens.Lens' (Vec ('S n) a) a
_head f (x ::: xs) = (::: xs) <$> f x
{-# INLINE _head #-}

-- | Head lens. /Note:/ @lens@ 'Lens._head' is a 'Lens.Traversal''.
_tail :: Lens.Lens' (Vec ('S n) a) (Vec n a)
_tail f (x ::: xs) = (x :::) <$> f xs
{-# INLINE _tail #-}

-------------------------------------------------------------------------------
-- Generic traversable with index
-------------------------------------------------------------------------------

-- | Generic traverse.
--
-- __Don't use__, rather use @DeriveTraversable@
gtraverse
    :: ( G.Generic1 t, GFrom t, GTo t
       , N.SNatI (GPigeonholeSize t)
       , Applicative f
       )
    => (a -> f b) -> t a -> f (t b)
gtraverse = confusing $ \afb ta -> gto <$> V.traverse afb (gfrom ta)
{-# INLINE gtraverse #-}

-- | Traverse with index.
--
-- >>> data Key = Key1 | Key2 | Key3 deriving (Show, Generic)
-- >>> data Values a = Values a a a deriving (Generic1)
--
-- >>> gitraverse (\i a -> Const [(i :: Key, a)]) (Values 'a' 'b' 'c')
-- Const [(Key1,'a'),(Key2,'b'),(Key3,'c')]
--
gitraverse
    :: ( G.Generic i, F.GTo i
       , G.Generic1 t, GFrom t, GTo t
       , F.GEnumSize i ~ GPigeonholeSize t, N.SNatI (GPigeonholeSize t)
       , Applicative f
       )
    => (i -> a -> f b) -> t a -> f (t b)
gitraverse = iconfusing $ \iafb ta -> gto <$> V.itraverse (\i a -> iafb (F.gto i) a) (gfrom ta)
{-# INLINE gitraverse #-}

-------------------------------------------------------------------------------
-- PigeonholeSize
-------------------------------------------------------------------------------

-- | Compute the size from the type.
type GPigeonholeSize c = PigeonholeSizeRep (G.Rep1 c) N.Nat0

type family PigeonholeSizeRep (c :: * -> *) (n :: Nat) :: Nat where
    PigeonholeSizeRep (a :*: b )   n = PigeonholeSizeRep a (PigeonholeSizeRep b n)
    PigeonholeSizeRep (M1 _d _c a) n = PigeonholeSizeRep a n
    PigeonholeSizeRep Par1         n = 'N.S n
    PigeonholeSizeRep U1           n = n

-------------------------------------------------------------------------------
-- From
-------------------------------------------------------------------------------

-- | Generic version of 'from'.
gfrom :: (G.Generic1 c, GFrom c) => c a -> Vec (GPigeonholeSize c) a
gfrom = \x -> gfromRep1 (G.from1 x) VNil

-- | Constraint for the class that computes 'gfrom'.
type GFrom c = GFromRep1 (G.Rep1 c)

class GFromRep1 (c :: * -> *)  where
    gfromRep1 :: c x -> Vec n x -> Vec (PigeonholeSizeRep c n) x

instance (GFromRep1 a, GFromRep1 b) => GFromRep1 (a :*: b) where
    gfromRep1 (x :*: y) z = gfromRep1 x (gfromRep1 y z)

instance GFromRep1 a => GFromRep1 (M1 d c a) where
    gfromRep1 (M1 a) z = gfromRep1 a z

instance GFromRep1 Par1 where
    gfromRep1 (Par1 x) z = x ::: z

instance GFromRep1 U1 where
    gfromRep1 _U1 z = z

-------------------------------------------------------------------------------
-- To
-------------------------------------------------------------------------------

-- | Generic version of 'to'.
gto :: forall c a. (G.Generic1 c, GTo c) => Vec (GPigeonholeSize c) a -> c a
gto = \xs -> G.to1 $ fst (gtoRep1 xs :: (G.Rep1 c a, Vec 'N.Z a))

-- | Constraint for the class that computes 'gto'.
type GTo c = GToRep1 (G.Rep1 c)

class GToRep1 (c :: * -> *) where
    gtoRep1 :: Vec (PigeonholeSizeRep c n) x -> (c x, Vec n x)

instance GToRep1 a => GToRep1 (M1 d c a) where
    gtoRep1 = first M1 . gtoRep1

instance (GToRep1 a, GToRep1 b) => GToRep1 (a :*: b) where
    gtoRep1 xs =
        let (a, ys) = gtoRep1 xs
            (b, zs) = gtoRep1 ys
        in (a :*: b, zs)

instance GToRep1 Par1 where
    gtoRep1 (x ::: xs) = (Par1 x, xs)

instance GToRep1 U1 where
    gtoRep1 xs = (U1, xs)
