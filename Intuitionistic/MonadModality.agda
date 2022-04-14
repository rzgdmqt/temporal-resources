-------------------------------------------------------------------
-- Semantics of the context modality `Γ ⟨ t ⟩` as a graded monad --
-------------------------------------------------------------------

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

module MonadModality where

⟨_⟩ᵒ : Time → TSet → TSet
⟨ τ ⟩ᵒ (tset A Af) =
  tset
    (λ t' → τ ≤ t' × A (t' ∸ τ))
    (λ p (q , a) → ≤-trans q p , Af (∸-mono p (≤-refl {τ})) a)

⟨_⟩ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → ⟨ τ ⟩ᵒ A →ᵗ ⟨ τ ⟩ᵒ B
⟨ τ ⟩ᶠ (tset-map f) =
  tset-map
    (λ { (p , a) → p , f a })

⟨_⟩-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → ⟨ τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ A
⟨_⟩-≤ {tset A Af} p =
  tset-map
    (λ { {t} (q , a) → ≤-trans p q , Af (∸-mono (≤-refl {t}) p) a })

η : ∀ {A} → A →ᵗ ⟨ 0 ⟩ᵒ A
η =
  tset-map
    (λ a → z≤n , a)

η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵗ A
η⁻¹ =
  tset-map
    (λ { (p , a) → a })

μ : ∀ {A τ₁ τ₂} → ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A) →ᵗ ⟨ τ₁ + τ₂ ⟩ᵒ A
μ {tset A Af} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , q , a) → n≤k⇒m≤k∸n⇒n+m≤k τ₁ τ₂ t p q ,
                           Af (≤-reflexive (n∸m∸k≡n∸m+k t τ₁ τ₂)) a })

μ⁻¹ : ∀ {A τ₁ τ₂} → ⟨ τ₁ + τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A)
μ⁻¹ {tset A Af} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , a) → m+n≤o⇒m≤o τ₁ p ,
                       n+m≤k⇒m≤k∸n τ₁ τ₂ t p ,
                       Af (≤-reflexive (sym (n∸m∸k≡n∸m+k t τ₁ τ₂))) a })
