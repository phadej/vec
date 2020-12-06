module Vec where

open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- "GADT"
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 50 _∷_

exVec : Vec ℕ 2
exVec = 13 ∷ 37 ∷ []

-- "data family"
data Unit : Set where
  [] : Unit

data _×_ (A B : Set) : Set where
  _∷_ : A → B → A × B

infixr 50 _×_

VecF : Set → ℕ → Set
VecF A zero    = Unit
VecF A (suc n) = A × VecF A n

exVecF : VecF ℕ 2
exVecF = 13 ∷ 37 ∷ []

reduction : VecF ℕ 2 ≡ ℕ × ℕ × Unit
reduction = refl
