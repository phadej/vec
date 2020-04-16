{-# LANGUAGE CPP        #-}
{-# LANGUAGE RankNTypes #-}
-- | A small module defining the least you need to support
-- van-Laarhoven lenses without depending on @lens@ or @microlens@ or ...
--
-- See @lens@ package for the documentation.
--
-- I copy this around.
--
-- Assumes GHC-7.8 / base-4.7; with "Data.Coerce".
--
-- <https://en.wikipedia.org/wiki/Yocto->
module Control.Lens.Yocto (
    -- * Types
    Optic, Optic',
    LensLike, LensLike',
    Lens, Lens',
    Traversal, Traversal',
#ifdef MIN_VERSION_profunctors
    Prism, Prism',
    Iso, Iso',
#endif
    -- * Operations
    view, set, over,
    -- * Operators
    (<&>),
    -- * Constructors
#ifdef MIN_VERSION_profunctors
    iso,
    prism,
    prism',
#endif
    )where

import Control.Applicative   (Applicative (..), Const (..))
import Data.Coerce           (coerce)
import Data.Functor.Identity (Identity (..))
import Prelude               (Functor (..), const, (.))

#ifdef MIN_VERSION_profunctors
import Data.Profunctor (Choice (..), Profunctor (..))
import Prelude         (Either (..), Maybe, either, maybe, (.))
#endif

#if MIN_VERSION_base(4,11,0)
import Data.Functor ((<&>))
#endif

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

type Optic p f s t a b = p a (f b) -> p s (f t)
type Optic' p f s a = Optic p f s s a a

type LensLike f s t a b = Optic (->) f s t a b
type LensLike' f s a = LensLike f s s a a

type Lens s t a b = forall f. Functor f => LensLike f s t a b
type Lens' s a = Lens s s a a

type Traversal s t a b = forall f. Applicative f => LensLike f s t a b
type Traversal' s a = Lens s s a a

#ifdef MIN_VERSION_profunctors
type Prism s t a b = forall p f. (Choice p, Applicative f) => Optic p f s t a b
type Prism' s a = Prism s s a a

type Iso s t a b = forall p f. (Profunctor p, Functor f) => Optic p f s t a b
type Iso' s a = Iso s s a a
#endif

-------------------------------------------------------------------------------
-- Operations
-------------------------------------------------------------------------------

view :: LensLike' (Const a) s a -> s -> a
view l = coerce (l Const)
{-# INLINE view #-}

set :: LensLike Identity s t a b -> b -> s -> t
set l = over l . const
{-# INLINE set #-}

over :: LensLike Identity s t a b -> (a -> b) -> s -> t
over = coerce
{-# INLINE over #-}

-------------------------------------------------------------------------------
-- Operators
-------------------------------------------------------------------------------

#if !MIN_VERSION_base(4,11,0)
(<&>) :: Functor f => f a -> (a -> b) -> f b
as <&> f = fmap f as

infixl 1 <&>
#endif

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

#ifdef MIN_VERSION_profunctors
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso sa bt = dimap sa (fmap bt)
{-# INLINE iso #-}

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (either pure (fmap bt)) . right'
{-# INLINE prism #-}

prism' :: (b -> s) -> (s -> Maybe a) -> Prism s s a b
prism' bs sma = prism bs (\s -> maybe (Left s) Right (sma s))
{-# INLINE prism' #-}
#endif
