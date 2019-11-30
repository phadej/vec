{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.RAL.Lens (
    -- * Indexing
    ix,
    ixNE,
    ) where

import Control.Applicative ((<$>))
import Data.Bin.Pos        (Pos (..), PosN (..), PosN' (..))
import Prelude ()

import qualified Control.Lens       as L
import qualified Data.RAL.Tree.Lens as Tree

import Data.RAL

-- $setup
-- >>> import Control.Lens ((^.), (&), (.~), (^?), (#))
-- >>> import Prelude
-- >>> import qualified Data.Type.Bin as B

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

-- | Index lens.
--
-- >>> let Just ral = fromList "xyz" :: Maybe (RAL B.Bin3 Char)
-- >>> ral & ix maxBound .~ 'Z'
-- NonEmpty (Cons1 (Leaf 'x') (Last (Node (Leaf 'y') (Leaf 'Z'))))
ix :: Pos b -> L.Lens' (RAL b a) a
ix (Pos (PosN n)) f (NonEmpty x) = NonEmpty <$> ixNE n f x

ixNE :: PosN' n b -> L.Lens' (NERAL n b a) a
ixNE (AtEnd i)  f (Last  t)   = Last <$> Tree.ix i f t
ixNE (There0 i) f (Cons0   r) = Cons0 <$> ixNE i f r
ixNE (There1 i) f (Cons1 t r) = (t `Cons1`) <$> ixNE i f r
ixNE (Here i)   f (Cons1 t r) = (`Cons1` r) <$> Tree.ix i f t

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance L.FunctorWithIndex (Pos b) (RAL b) where
    imap = imap

instance L.FunctorWithIndex (PosN' n b) (NERAL n b) where
    imap = imapNE

instance L.FoldableWithIndex (Pos b) (RAL b) where
    ifoldMap = ifoldMap
    ifoldr   = ifoldr

instance L.FoldableWithIndex (PosN' n b) (NERAL n b) where
    ifoldMap = ifoldMapNE
    ifoldr   = ifoldrNE

instance L.TraversableWithIndex (Pos b) (RAL b) where
    itraverse = itraverse

instance L.TraversableWithIndex (PosN' n b) (NERAL n b) where
    itraverse = itraverseNE

instance L.Each (RAL n a) (RAL n b) a b where
    each = traverse

instance L.Each (NERAL n m a) (NERAL n m b) a b where
    each = traverseNE

type instance L.Index   (RAL n a) = Pos n
type instance L.IxValue (RAL n a) = a

type instance L.Index   (NERAL n b a) = PosN' n b
type instance L.IxValue (NERAL n b a) = a

instance L.Ixed (RAL b a) where
    ix = ix

instance L.Ixed (NERAL n b a) where
    ix = ixNE
