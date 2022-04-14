------------------------------------------------------------------
-- Semantics of the type modality `[ t ] A` as a graded comonad --
------------------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Language
open import TSets

module ComonadModality where

-- Functor

[_]ᵒ : Time → TSet → TSet
[ τ ]ᵒ A =
  tset
    (λ t' → carrier A (t' + τ))
    (λ p a → monotone A (+-mono-≤ p ≤-refl) a)
    (λ x → trans
             (cong (λ p → monotone A p x) (≤-irrelevant _ ≤-refl))
             (monotone-refl A x))
    (λ p q x → trans
                 (monotone-trans A _ _ x)
                 (cong
                   (λ r → monotone A r x)
                   (≤-irrelevant _ (+-mono-≤ (≤-trans p q) ≤-refl))))

[_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → [ τ ]ᵒ A →ᵗ [ τ ]ᵒ B
[ τ ]ᶠ (tset-map f) = tset-map f

-- Monotonicity for gradings

[_]-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵗ [ τ₂ ]ᵒ A
[_]-≤ {A} p =
  tset-map
    (λ a → monotone A (+-mono-≤ ≤-refl p) a)

-- Counit

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {A} =
  tset-map
    (λ {t} a → monotone A (≤-reflexive (+-identityʳ t)) a)

ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A
ε⁻¹ {A} =
  tset-map
    (λ {t} a → monotone A (≤-reflexive (sym (+-identityʳ t))) a)

-- Comultiplication

δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵗ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
δ {A} {τ₁} {τ₂} =
  tset-map
    (λ {t} a → monotone A (≤-reflexive (sym (+-assoc t τ₁ τ₂))) a)

δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵗ [ τ₁ + τ₂ ]ᵒ A
δ⁻¹ {A} {τ₁} {τ₂} =
  tset-map (λ {t} a → monotone A (≤-reflexive (+-assoc t τ₁ τ₂)) a)

-- Properties

---- counit is an isomorphism

--ε-∘ᵗ-ε' : ∀ {A} → ε {A = A} ∘ᵗ ε⁻¹ ≡ᵗ idᵗ
--ε-∘ᵗ-ε' = λ x → {!!}
