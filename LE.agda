{-# OPTIONS --cubical --safe #-}
module LE where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Nat
  using (ℕ; zero; isSetℕ; _+_; +-zero; +-suc)
  renaming (suc to succ; inj-m+ to +-inj₁; inj-+m to +-inj₂; injSuc to succ-inj; snotz to ¬succ≡zero)

module ZeroSucc where
  data _≤_ : ℕ → ℕ → Type₀ where
    leZero : ∀ {m} → zero ≤ m
    leSucc : ∀ {n m} → n ≤ m → succ n ≤ succ m

  leRefl : ∀ n → n ≤ n
  leRefl zero     = leZero
  leRefl (succ n) = leSucc (leRefl n)

  leStep : ∀ {n m} → n ≤ m → n ≤ succ m
  leStep leZero     = leZero
  leStep (leSucc p) = leSucc (leStep p)

  lePred : ∀ {n m} → succ n ≤ succ m → n ≤ m
  lePred (leSucc p) = p

  lePlus : ∀ p n m → p + n ≡ m → n ≤ m
  lePlus zero     n _ p+n≡m = subst (n ≤_) p+n≡m (leRefl n)
  lePlus (succ p) zero     zero     p+n≡m = leZero
  lePlus (succ p) (succ n) zero     p+n≡m = ⊥-elim (¬succ≡zero p+n≡m)
  lePlus (succ p) n        (succ m) p+n≡m = leStep (lePlus p n m (succ-inj p+n≡m))

  decide-≤ : ∀ n m → Dec (n ≤ m)
  decide-≤ zero m = yes leZero
  decide-≤ (succ n) zero = no (λ ())
  decide-≤ (succ n) (succ m) with decide-≤ n m
  ... | yes p = yes (leSucc p)
  ... | no ¬p = no (λ p → ¬p (lePred p))

  isProp-≤ : ∀ {n m} → isProp (n ≤ m)
  isProp-≤ leZero     leZero     = refl
  isProp-≤ (leSucc p) (leSucc q) = cong leSucc (isProp-≤ p q) 
  
module ReflStep where
  data _≤_ : ℕ → ℕ → Type₀ where
    leRefl : ∀ {n} → n ≤ n
    leStep : ∀ {n m} → n ≤ m → n ≤ succ m

  leZero : ∀ m → zero ≤ m
  leZero zero     = leRefl
  leZero (succ m) = leStep (leZero m)

  leSucc : ∀ {n m} → n ≤ m → succ n ≤ succ m
  leSucc leRefl = leRefl
  leSucc (leStep p) = leStep (leSucc p)

  -- Path between ReflStep and ZeroSucc
  toZS : ∀ {n m} → n ≤ m → n ZeroSucc.≤ m
  toZS leRefl     = ZeroSucc.leRefl _
  toZS (leStep p) = ZeroSucc.leStep (toZS p)

  fromZS : ∀ {n m} → n ZeroSucc.≤ m → n ≤ m
  fromZS ZeroSucc.leZero     = leZero _
  fromZS (ZeroSucc.leSucc p) = leSucc (fromZS p)

  to∘from : ∀ {n m} (x : n ZeroSucc.≤ m) → toZS (fromZS x) ≡ x
  to∘from x = ZeroSucc.isProp-≤ _ x

  from∘to : ∀ {n m} (x : n ≤ m) → fromZS (toZS x) ≡ x
  from∘to leRefl = lemma _ where
    lemma : ∀ m → fromZS (ZeroSucc.leRefl m) ≡ leRefl
    lemma zero     = refl
    lemma (succ m) = cong leSucc (lemma m)
  from∘to (leStep x) = lemma (toZS x) ∙ cong leStep (from∘to x) where
    lemma : ∀ {n m} → (p : n ZeroSucc.≤ m) → fromZS (ZeroSucc.leStep p) ≡ leStep (fromZS p)
    lemma ZeroSucc.leZero     = refl
    lemma (ZeroSucc.leSucc p) = cong leSucc (lemma p)

  ≡ZeroSucc : _≤_ ≡ ZeroSucc._≤_
  ≡ZeroSucc = funExt λ n → funExt λ m → isoToPath (iso toZS fromZS to∘from from∘to)

  isProp-≤ : ∀ {n m} → isProp (n ≤ m)
  isProp-≤ {n} {m} = subst (λ R → isProp (R n m)) (sym ≡ZeroSucc) ZeroSucc.isProp-≤

module ExistsSum where
  data _≤_ : ℕ → ℕ → Type₀ where
    exists : ∀ {n m} p → p + n ≡ m → n ≤ m

  leZero : ∀ m → zero ≤ m
  leZero m = exists m (+-zero m)

  leSucc : ∀ {n m} → n ≤ m → succ n ≤ succ m
  leSucc (exists p x) = exists p (+-suc p _ ∙ cong succ x)

  toZS : ∀ {n m} → n ≤ m → n ZeroSucc.≤ m
  toZS (exists p x) = ZeroSucc.lePlus p _ _ x

  fromZS : ∀ {n m} → n ZeroSucc.≤ m → n ≤ m
  fromZS ZeroSucc.leZero     = leZero _
  fromZS (ZeroSucc.leSucc p) = leSucc (fromZS p)

  to∘from : ∀ {n m} (x : n ZeroSucc.≤ m) → toZS (fromZS x) ≡ x
  to∘from x = ZeroSucc.isProp-≤ _ x

  isProp-≤ : ∀ {n m} → isProp (n ≤ m)
  isProp-≤ {n} {m} (exists p pp) (exists q qq) i =
    exists (lemma₁ i) (lemma₂ i) 
    where
      lemma₁ : p ≡ q
      lemma₁ = +-inj₂ (pp ∙ sym qq)

      lemma₂ : PathP (λ i → lemma₁ i + n ≡ m) pp qq
      lemma₂ = isOfHLevel→isOfHLevelDep
        {n = 1} {A = ℕ} {B = λ p → p + n ≡ m}
        (λ a → isSetℕ _ _) pp qq lemma₁

  from∘to : ∀ {n m} → (x : n ≤ m) → fromZS (toZS x) ≡ x
  from∘to x = isProp-≤ _ x

  ≡ZeroSucc : _≤_ ≡ ZeroSucc._≤_
  ≡ZeroSucc = funExt λ n → funExt λ m → isoToPath (iso toZS fromZS to∘from from∘to)

  ≡ReflStep : _≤_ ≡ ReflStep._≤_
  ≡ReflStep = ≡ZeroSucc ∙ sym ReflStep.≡ZeroSucc
