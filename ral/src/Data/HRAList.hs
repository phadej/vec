{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.HRAList where

import Data.Kind            (Type)
import Data.RAList.NonEmpty (NERAList (..), NERAList' (..))
import Data.RAList.Tree     (Leaf (..), Node (..))

-- * Types

-- | Heterogenous perfect binary tree.
data HTree (tr :: Type -> Type) (t :: tr k) (f :: k -> Type) :: Type where
    HLeaf :: f x                            -> HTree Leaf      ('Lf x)     f
    HNode :: HTree tr xs f -> HTree tr ys f -> HTree (Node tr) ('Nd xs ys) f

-- | Heterogenous non-empty random access list.
data HNERAList (ral :: NERAList k) (f :: k -> Type) where
    HNE :: HNERAList' Leaf ral f -> HNERAList ('NE ral) f

-- | Heterogenous non-empty random access list, underlying structure.
data HNERAList' (tr :: Type -> Type) (ral :: NERAList' tr k) (f :: k -> Type) :: Type where
    HLast  :: HTree tr t f                             -> HNERAList' tr ('Last t)    f
    HCons0 ::                 HNERAList' (Node tr) r f -> HNERAList' tr ('Cons0   r) f
    HCons1 :: HTree tr t f -> HNERAList' (Node tr) r f -> HNERAList' tr ('Cons1 t r) f

-- * Type level consing

-- | Lifted 'Data.RAList.NonEmpty.cons'.
type family Cons (x :: k) (r :: NERAList k) :: NERAList k where
    Cons x ('NE r) = 'NE (Cons' x r)

type Cons' (x :: k) (r :: NERAList' Leaf k) = ConsTree Leaf ('Lf x) r

type family ConsTree (tr :: Type -> Type) (t :: tr k) (r :: NERAList' tr k) :: NERAList' tr k where
    ConsTree tr x ('Last  t)   = 'Cons0 ('Last ('Nd x t))
    ConsTree tr x ('Cons0   r) = 'Cons1 x r
    ConsTree tr x ('Cons1 t r) = 'Cons0 (ConsTree (Node tr) ('Nd x t) r)

-- * Term level consing

-- | Cons value to the hral.
cons :: f x -> HNERAList r f -> HNERAList (Cons x r) f
cons fx (HNE r) = HNE (cons' fx r)

cons' :: f x -> HNERAList' Leaf r f -> HNERAList' Leaf (Cons' x r) f
cons' = consTree . HLeaf

consTree :: HTree tr t f -> HNERAList' tr r f -> HNERAList' tr (ConsTree tr t r) f
consTree x (HLast  t)   = HCons0 (HLast (HNode x t))
consTree x (HCons0   r) = HCons1 x r
consTree x (HCons1 t r) = HCons0 (consTree (HNode x t) r)
