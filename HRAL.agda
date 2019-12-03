module HRAL where

open import Level

-- Tree using two types, polymorphic recurson

record Leaf {a} (A : Set a) : Set a where
  constructor lf
  field
    lf' : A

open Leaf

record Node {a} (F : Set a -> Set a) (A : Set a) : Set a where
  constructor nd
  field
    lft : F A
    rgt : F A

open Node

-- non-empty random access list

data NERAL' {a} (tr : Set a -> Set a) (A : Set a) : Set a where
  Last  : tr A                      → NERAL' tr A
  Cons0 :        NERAL' (Node tr) A → NERAL' tr A
  Cons1 : tr A → NERAL' (Node tr) A → NERAL' tr A

consTree : ∀ {a} {A : Set a} {tr} → tr A → NERAL' tr A → NERAL' tr A
consTree x (Last  t)   = Cons0 (Last (nd x t))
consTree x (Cons0   r) = Cons1 x r
consTree x (Cons1 t r) = Cons0 (consTree (nd x t) r)

cons : ∀ {a} {A : Set a} → A → NERAL' Leaf A → NERAL' Leaf A
cons x = consTree (lf x)

-- heterogenous Tree

data HTree {k} {K : Set k} (f : K -> Set) : (tr : Set k → Set k) → tr K -> Set (suc k) where
  HLf : ∀ {x : K}    → f x → HTree f Leaf (lf x)
  HNd : ∀ {tr xs ys} → HTree f tr xs → HTree f tr ys → HTree f (Node tr) (nd xs ys)

-- heterogenous non-empty random access list

data HNERAL' {k} {K : Set k} (f : K → Set) : (tr : Set k → Set k) → NERAL' tr K → Set (suc k) where
  HLast  : ∀ {tr t}   → HTree f tr t                         → HNERAL' f tr (Last  t)
  HCons0 : ∀ {tr   r} →                HNERAL' f (Node tr) r → HNERAL' f tr (Cons0   r)
  HCons1 : ∀ {tr t r} → HTree f tr t → HNERAL' f (Node tr) r → HNERAL' f tr (Cons1 t r)

hconsTree : ∀ {k} {K : Set k} {f : K → Set} {tr t r}
          → HTree f tr t → HNERAL' f tr r → HNERAL' f tr (consTree t r)
hconsTree x (HLast   t)  = HCons0 (HLast (HNd x t))
hconsTree x (HCons0   r) = HCons1 x r
hconsTree x (HCons1 t r) = HCons0 (hconsTree (HNd x t) r)

hcons : ∀ {k} {K : Set k} {f : K → Set} {x r}
      → f x → HNERAL' f Leaf r → HNERAL' f Leaf (cons x r)
hcons fx = hconsTree (HLf fx)
