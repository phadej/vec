{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeInType #-}

module Data.HRAL (
    -- * Heterogenous Tree
    HTree (..),
    HTreePath (..),
    -- ** Tree Singleton
    -- Used to define instances for HTRee
    STree (..), STreeI (..),
    -- ** Lookup
    hindexTree,
    -- ** Heterogenous RAL
    HRAL (..),
    HNERAL (..),
    -- ** Simple constructor
    empty,
    singleton,
    -- ** Cons 
    Cons, ConsN, ConsTree,
    cons, consI,
    consTree,
    -- ** Positions
    Pos (..),
    PosN (..),
    -- ** Top and pop
    top,
    pop,
    -- * Test
    (:>), Nil,
    demoHRAL,
    test1,
    test2,
    -- ** Well-typed term / expression
    Expr (..),
    eval,
    ) where

import Data.Bin      (Bin (..), BinN (..))
import Data.Type.Bin (Succ, Succ', SuccN')
import Data.HKD
       (FFoldable (..), FFunctor (..), FRepeat (..), FTraversable (..),
       FZip (..))
import Data.Kind     (Type)
import Data.Functor.Identity (Identity (..))
import Data.Nat      (Nat (..))
import Data.RAL      (NERAL (..), RAL (..))
import Data.RAL.Tree (Tree (..))

data HTree (n :: Nat) (t :: Tree n k) (f :: k -> Type) where
    HLeaf :: f z ->                          HTree 'Z     ('Leaf z)     f
    HNode :: HTree n xs f -> HTree n ys f -> HTree ('S n) ('Node xs ys) f

-------------------------------------------------------------------------------
-- Tree singleton
-------------------------------------------------------------------------------

data STree (n :: Nat) (t :: Tree n k) where
    SLeaf :: STree 'Z ('Leaf a)
    SNode :: STree n xs -> STree n ys -> STree ('S n) ('Node xs ys)

class                                  STreeI (n :: Nat) (t :: Tree n k) where stree :: STree n t
instance                               STreeI 'Z         ('Leaf a)       where stree = SLeaf
instance (STreeI n xs, STreeI n ys) => STreeI ('S n)     ('Node xs ys)   where stree = SNode stree stree

-------------------------------------------------------------------------------
-- Instances: HKD
-------------------------------------------------------------------------------

instance FFunctor (HTree n t) where
    ffmap f (HLeaf x)     = HLeaf (f x)
    ffmap f (HNode xs ys) = HNode (ffmap f xs) (ffmap f ys)

instance FFoldable (HTree n t) where
    ffoldMap f (HLeaf x)     = f x
    ffoldMap f (HNode xs ys) = ffoldMap f xs `mappend` ffoldMap f ys

instance FTraversable (HTree n t) where
    ftraverse f (HLeaf x)     = HLeaf <$> f x
    ftraverse f (HNode xs ys) = HNode <$> ftraverse f xs <*> ftraverse f ys

instance FZip (HTree n t) where
    fzipWith f (HLeaf x)     (HLeaf y)     = HLeaf (f x y)
    fzipWith f (HNode xs ys) (HNode us vs) = HNode (fzipWith f xs us) (fzipWith f ys vs)

instance STreeI n t => FRepeat (HTree n t) where
    frepeat = go stree where
        go :: forall m f t'. STree m t' -> (forall x. f x) -> HTree m t' f
        go SLeaf         x = HLeaf x
        go (SNode xs ys) x = HNode (go xs x) (go ys x)

-------------------------------------------------------------------------------
-- Path
-------------------------------------------------------------------------------

data HTreePath n (t :: Tree n k) (a :: k) where
    HHere  ::                     HTreePath 'Z     ('Leaf z)     z
    HLeft  :: -- forall (n :: Nat) (xs :: Tree n k) (ys :: Tree n k) (a :: k).
              HTreePath n xs a -> HTreePath ('S n) ('Node xs ys) a
    HRight :: -- forall (n :: Nat) (xs :: Tree n k) (ys :: Tree n k) (a :: k).
              HTreePath n ys a -> HTreePath ('S n) ('Node xs ys) a

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

hindexTree :: HTree n t f -> HTreePath n t a -> f a
hindexTree (HLeaf x)    HHere      = x
hindexTree (HNode xs _) (HLeft i)  = hindexTree xs i
hindexTree (HNode _ ys) (HRight j) = hindexTree ys j

-------------------------------------------------------------------------------
-- HRAL
-------------------------------------------------------------------------------

-- | Will 'HRAL' work without explicit @b@?
data HRAL (b :: Bin) (ral :: RAL b k) (f :: k -> Type) where
    HEmpty    ::                      HRAL 'BZ     'Empty          f
    HNonEmpty :: HNERAL 'Z b ral f -> HRAL ('BN b) ('NonEmpty ral) f

data HNERAL (n :: Nat) (b :: BinN) (ral :: NERAL n b k) (f :: k -> Type) where
    HLast  :: HTree n t f                          -> HNERAL n 'BE     ('Last t)      f
    HCons0 ::                HNERAL ('S n) b ral f -> HNERAL n ('B0 b) ('Cons0 ral)   f
    HCons1 :: HTree n t f -> HNERAL ('S n) b ral f -> HNERAL n ('B1 b) ('Cons1 t ral) f

-------------------------------------------------------------------------------
-- HRAL: instances
-------------------------------------------------------------------------------

instance FFunctor (HRAL b ral) where
    ffmap _ HEmpty = HEmpty
    ffmap f (HNonEmpty r) = HNonEmpty (ffmap f r)

instance FFunctor (HNERAL n b ral) where
    ffmap f (HLast  t)   = HLast (ffmap f t)
    ffmap f (HCons0   r) = HCons0 (ffmap f r)
    ffmap f (HCons1 t r) = HCons1 (ffmap f t) (ffmap f r)

-- TODO: up to FRepeat

-------------------------------------------------------------------------------
-- Pos
-------------------------------------------------------------------------------

-- | TODO: HPos...
data Pos (b :: Bin) (ral :: RAL b k) (a :: k) where
    Pos :: PosN 'Z b ral a -> Pos ('BN b) ('NonEmpty ral) a

data PosN (n :: Nat) (b :: BinN) (ral :: NERAL n b k) (a :: k) where
    AtEnd  :: HTreePath n t a   -> PosN n 'BE     ('Last  t)   a
    Here   :: HTreePath n t a   -> PosN n ('B1 b) ('Cons1 t r) a
    There1 :: PosN ('S n) b r a -> PosN n ('B1 b) ('Cons1 t r) a
    There0 :: PosN ('S n) b r a -> PosN n ('B0 b) ('Cons0   r) a

hindex :: HRAL b ral f -> Pos b ral a -> f a
hindex (HNonEmpty r) (Pos p) = hindexN r p
hindex HEmpty        p       = case p of {}

hindexN :: HNERAL n b ral f -> PosN n b ral a -> f a
hindexN (HLast  t)   (AtEnd p)  = hindexTree t p
hindexN (HCons0   r) (There0 p) = hindexN r p
hindexN (HCons1 _ r) (There1 p) = hindexN r p
hindexN (HCons1 t _) (Here p)   = hindexTree t p

-------------------------------------------------------------------------------
-- Cons
-------------------------------------------------------------------------------

-- We'd like to specify explicit @b@ indices here, but then we cannot make
-- 'Cons' into ':>'.
type family Cons (x :: k) (ral :: RAL b k) :: RAL ('BN (Succ' b)) k where
    Cons x 'Empty        = 'NonEmpty ('Last ('Leaf x))
    Cons x ('NonEmpty r) = 'NonEmpty (ConsN x r)

type family ConsN (x :: k) (ral :: NERAL 'Z b k) :: NERAL 'Z (SuccN' b) k where
    ConsN x ral = ConsTree 'Z ('Leaf x) ral

type family ConsTree (n :: Nat) (t :: Tree n k) (ral :: NERAL n b k) :: NERAL n (SuccN' b) k where
    ConsTree n x ('Last  t)   = 'Cons0 ('Last ('Node x t))
    ConsTree n x ('Cons0   r) = 'Cons1 x r
    ConsTree n x ('Cons1 t r) = 'Cons0 (ConsTree ('S n) ('Node x t) r)

empty :: HRAL 'BZ 'Empty f
empty = HEmpty

singleton :: f a -> HRAL ('BN 'BE) ('NonEmpty ('Last ('Leaf a))) f
singleton x = HNonEmpty (HLast (HLeaf x))

cons :: f a -> HRAL b ral f -> HRAL (Succ b) (Cons a ral) f
cons x HEmpty        = HNonEmpty (HLast (HLeaf x))
cons x (HNonEmpty r) = HNonEmpty (consTree (HLeaf x) r)

consI :: a -> HRAL b ral Identity -> HRAL (Succ b) (Cons a ral) Identity
consI = cons . Identity

consTree :: HTree n t f -> HNERAL n b ral f -> HNERAL  n (SuccN' b) (ConsTree n t ral) f
consTree x (HLast  t)   = HCons0 (HLast (HNode x t))
consTree x (HCons0   r) = HCons1 x r
consTree x (HCons1 t r) = HCons0 (consTree (HNode x t) r)

-------------------------------------------------------------------------------
-- Top
-------------------------------------------------------------------------------

class Top (ral :: RAL b k) (a :: k) where
    top :: Pos b ral a

instance TopN ral a => Top ('NonEmpty ral) a where
    top = Pos topN

class TopN (ral :: NERAL n b k) (a :: k) where
    topN :: PosN n b ral a

instance TopTree t a => TopN ('Last t) (a :: k) where
    topN = AtEnd topTreePath

instance TopN t a => TopN ('Cons0 t) a where
    topN = There0 topN

instance TopTree t a => TopN ('Cons1 t r) a where
    topN = Here topTreePath

class TopTree (t :: Tree n k) (a :: k) where
    topTreePath :: HTreePath n t a

instance a ~ b => TopTree ('Leaf a) b where
    topTreePath = HHere

instance TopTree l a => TopTree ('Node l r) a where
    topTreePath = HLeft topTreePath

-------------------------------------------------------------------------------
-- Pop
-------------------------------------------------------------------------------

class b' ~ Succ b => Pop b (ral :: RAL b k) b' (ral' :: RAL b' k) | ral' -> ral where
    pop :: Pos b ral a -> Pos b' ral' a

instance PopN b ral b' ral' => Pop ('BN b) ('NonEmpty ral) ('BN b') ('NonEmpty ral') where
    pop (Pos p) = Pos (popN p)

class b' ~ SuccN' b => PopN b (ral :: NERAL n b k) b' (ral' :: NERAL n b' k) | ral' -> ral where
    popN :: PosN n b ral a -> PosN n b' ral' a

instance ral ~ ral' => PopN ('B0 b) ('Cons0 ral) ('B1 b) ('Cons1 t ral') where
    popN (There0 p) = There1 p

instance PopN0 b ral b' ral' => PopN b ral ('B0 b') ('Cons0 ral') where
    popN p = popN0 p

class 'B0 b' ~ SuccN' b => PopN0 b (ral :: NERAL n b k) b' (ral' :: NERAL ('S n) b' k) | ral' -> ral  where
    popN0 :: PosN n b ral a -> PosN n ('B0 b') ('Cons0 ral') a

instance PopN0 'BE ('Last t) 'BE ('Last ('Node x t)) where
    popN0 (AtEnd t) = There0 (AtEnd (HRight t))

instance PopN0 ('B1 ('B0 b)) ('Cons1 t ('Cons0 ral)) ('B1 b) ('Cons1 ('Node t' t) ral) where
    popN0 (Here p)            = There0 (Here (HRight p))
    popN0 (There1 (There0 p)) = There0 (There1 p)

instance
    ( PopN0 b ral b' ral'
    , PopTree ('Node ('Node tl t) tr) ral'
    )
    => PopN0 ('B1 b) ('Cons1 t ral) ('B0 b') ('Cons0 ral')
  where
    popN0 (There1 p) = There0 (popN0 p)
    popN0 (Here v)   = There0 (popTree (HRight v))

-- instance
--     ( PopN0 ral ral'
--     , PopTree ('Node t' t) ral'
--     ) => PopN0 ('Cons1 t ral) ('Cons0 ral') where

class PopTree (t :: Tree n k) (ral :: NERAL n b k) | ral -> t where
    popTree :: HTreePath n t a -> PosN n b ral a

instance PopTree t ('Last t) where
    popTree p = AtEnd p

instance PopTree t ('Cons1 t ral) where
    popTree p = Here p

instance PopTree ('Node t t') ral => PopTree t ('Cons0 ral) where
    popTree p = There0 (popTree (HLeft p))

-------------------------------------------------------------------------------
-- Test
-------------------------------------------------------------------------------

type x :> ral = Cons x ral
infixr 4 :>

type Nil = 'Empty

demoHRAL :: HRAL
    (Succ (Succ (Succ (Succ 'BZ))))
    (Bool :> Char :> Int :> String :> Nil)
    Identity
demoHRAL
    = consI True
    $ consI 'a'
    $ consI (3 :: Int)
    $ consI "foobar"
    $ empty

-- |
--
-- >>> hindex demoHRAL top
-- Identity True
--
-- >>> hindex demoHRAL $ pop top
-- Identity 'a'
--
-- >>> hindex demoHRAL $ pop $ pop top
-- Identity 3
--
-- >>> hindex demoHRAL $ pop $ pop $ pop top
-- Identity "foobar"
--
test1 :: Identity Bool
test1 = hindex demoHRAL $ top

test2 :: Identity Char
test2 = hindex demoHRAL $ pop top


-------------------------------------------------------------------------------
-- 
-------------------------------------------------------------------------------

data Expr (b :: Bin) (ctx :: RAL b f) (t :: Type) :: Type where
    Con :: a -> Expr b ctx a
    Var :: Pos b ctx a -> Expr b ctx a
    App :: Expr b ctx (a -> c) -> Expr b ctx a -> Expr b ctx c
    Lam :: Expr (Succ b) (a :> ctx) c -> Expr b ctx  (a -> c)

eval :: HRAL b ctx Identity -> Expr b ctx t -> t
eval _   (Con a)    = a
eval ctx (Var v)    = runIdentity (hindex ctx v)
eval ctx (App f x)  = eval ctx f (eval ctx x)
eval ctx (Lam body) = \v -> eval (cons (Identity v) ctx) body
