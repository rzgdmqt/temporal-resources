open import Function

open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

-- Time-indexed sets and modalities on them
-------------------------------------------

module TSets where

-- Time steps (using natural numbers)

Time : Set
Time = ℕ

-- Auxiliary lemmas

∸-+ : (n m k : ℕ) → n ∸ m ∸ k ≡ n ∸ (m + k)
∸-+ zero    zero    k       = refl
∸-+ zero    (suc m) zero    = refl
∸-+ zero    (suc m) (suc k) = refl
∸-+ (suc n) zero    k       = refl
∸-+ (suc n) (suc m) k       = ∸-+ n m k

+-∸ : (n m : ℕ) → n ≡ (n + m) ∸ m
+-∸ n m = 
  begin
    n
  ≡⟨ sym (+-identityʳ n) ⟩
    n + zero
  ≡⟨ cong (n +_) (sym (n∸n≡0 m)) ⟩
    n + (m ∸ m)
  ≡⟨ sym (+-∸-assoc n (≤-refl {m})) ⟩
    n + m ∸ m
  ∎

-- Time-indexed sets

record TSet : Set₁ where
  constructor
    tset
  field
    carrier  : Time → Set
    monotone : ∀ {t t'} → t ≤ t' → carrier t → carrier t'

    -- TODO: also include the functor laws for refl-id and trans-∘

open TSet

record _→ᵗ_ (A B : TSet) : Set where
  constructor
    tset-map
  field
    carrier : ∀ {t} → carrier A t → carrier B t

    -- TODO: also include naturality law

open _→ᵗ_

-- Semantics of `[ t ] A` modality as a graded comonad

[_]ᵒ : Time → TSet → TSet
[ t ]ᵒ (tset A Af) =
  tset
    (λ t' → A (t' + t))
    (λ p a → Af (+-mono-≤ p ≤-refl) a)

[_]ᶠ : ∀ {A B} → (t : Time) → A →ᵗ B → [ t ]ᵒ A →ᵗ [ t ]ᵒ B
[ t ]ᶠ (tset-map f) = tset-map f

[_]-≤ : ∀ {A t₁ t₂} → t₁ ≤ t₂ → [ t₁ ]ᵒ A →ᵗ [ t₂ ]ᵒ A
[_]-≤ {tset A Af} p =
  tset-map
    (λ a → Af (+-mono-≤ ≤-refl p) a)

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {tset A Af} =
  tset-map
    (λ {t} a → Af (≤-reflexive (+-identityʳ t)) a)

ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A
ε⁻¹ {tset A Af} =
  tset-map
    (λ {t} a → Af (≤-reflexive (sym (+-identityʳ t))) a)

δ : ∀ {A t₁ t₂} → [ t₁ + t₂ ]ᵒ A →ᵗ [ t₁ ]ᵒ ([ t₂ ]ᵒ A)
δ {tset A Af} {t₁} {t₂} =
  tset-map
    (λ {t} a → Af (≤-reflexive (sym (+-assoc t t₁ t₂))) a)

δ⁻¹ : ∀ {A t₁ t₂} → [ t₁ ]ᵒ ([ t₂ ]ᵒ A) →ᵗ [ t₁ + t₂ ]ᵒ A
δ⁻¹ {tset A Af} {t₁} {t₂} =
  tset-map (λ {t} a → Af (≤-reflexive (+-assoc t t₁ t₂)) a)

-- Semantics of `Γ ⟨ t ⟩` modality as a graded monad

⟨_⟩ᵒ : Time → TSet → TSet
⟨ t ⟩ᵒ (tset A Af) =
  tset
    (λ t' → A (t' ∸ t))
    (λ p a → Af (∸-mono p (≤-refl {t})) a)

⟨_⟩ᶠ : ∀ {A B} → (t : Time) → A →ᵗ B → ⟨ t ⟩ᵒ A →ᵗ ⟨ t ⟩ᵒ B
⟨ t ⟩ᶠ (tset-map f) = tset-map f

⟨_⟩-≤ : ∀ {A t₁ t₂} → t₁ ≤ t₂ → ⟨ t₂ ⟩ᵒ A →ᵗ ⟨ t₁ ⟩ᵒ A
⟨_⟩-≤ {tset A Af} p =
  tset-map
    (λ {t} a → Af (∸-mono (≤-refl {t}) p) a)

η : ∀ {A} → A →ᵗ ⟨ 0 ⟩ᵒ A
η = tset-map id

η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵗ A
η⁻¹ = tset-map id

μ : ∀ {A t₁ t₂} → ⟨ t₁ ⟩ᵒ (⟨ t₂ ⟩ᵒ A) →ᵗ ⟨ t₁ + t₂ ⟩ᵒ A
μ {tset A Af} {t₁} {t₂} =
  tset-map
    (λ {t} a → Af (≤-reflexive (∸-+ t t₁ t₂)) a)

μ⁻¹ : ∀ {A t₁ t₂} → ⟨ t₁ + t₂ ⟩ᵒ A →ᵗ ⟨ t₁ ⟩ᵒ (⟨ t₂ ⟩ᵒ A)
μ⁻¹ {tset A Af} {t₁} {t₂} =
  tset-map (λ {t} a → Af (≤-reflexive (sym (∸-+ t t₁ t₂))) a)

-- Graded monad and comonad are adjoint

η⊣ : ∀ {A t} → A →ᵗ [ t ]ᵒ (⟨ t ⟩ᵒ A)
η⊣ {tset A Af} {t} =
  tset-map
    (λ {t'} a → Af (≤-reflexive (+-∸ t' t)) a)

ε⊣ : ∀ {A t} → ⟨ t ⟩ᵒ ([ t ]ᵒ A) →ᵗ A
ε⊣ {tset A Af} {t} =
  tset-map
    (λ {t'} a → Af {!!} a)

-- ...
