-------------------------------------------------------------------
-- Semantics of the context modality `Γ ⟨ t ⟩` as a graded monad --
--                                                               --
-- While `Γ ⟨ t ⟩` is in fact a strong monoidal functor, then we --
-- prefer to speak abour it in terms of the graded monad view of --
-- it due to the analogy with the monad on contexts in Fitch     --
-- style modal lambda calculi (that this language is based on).  --
-------------------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Syntax.Language

open import Semantics.TSets

open import Util.Time

module Semantics.Modality.Past where

-- STRUCTURE

-- Functor

⟨_⟩ᵒ : Time → TSet → TSet
⟨ τ ⟩ᵒ (A) =
  tset
    (λ t' → τ ≤ t' × carrier A (t' ∸ τ))
    (λ p (q , a) → ≤-trans q p , monotone A (∸-mono p (≤-refl {τ})) a)
    (λ x → cong₂ _,_
             (≤-irrelevant _ _)
             (trans
               (cong (λ p → monotone A p (proj₂ x)) (≤-irrelevant _ _))
               (monotone-refl A (proj₂ x))))
    (λ p q x → cong₂ _,_
                 (≤-irrelevant _ _)
                 (trans
                   (monotone-trans A _ _ (proj₂ x))
                   (cong (λ r → monotone A r (proj₂ x)) (≤-irrelevant _ _))))

⟨_⟩ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → ⟨ τ ⟩ᵒ A →ᵗ ⟨ τ ⟩ᵒ B
⟨ τ ⟩ᶠ f =
  tset-map
    (λ { (p , a) → p , map-carrier f a })

-- (Contravariant) monotonicity for gradings

⟨_⟩-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → ⟨ τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ A
⟨_⟩-≤ {A} p =
  tset-map
    (λ { {t} (q , a) → ≤-trans p q , monotone A (∸-mono (≤-refl {t}) p) a })

-- Unit

η : ∀ {A} → A →ᵗ ⟨ 0 ⟩ᵒ A
η =
  tset-map
    (λ a → z≤n , a)

η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵗ A
η⁻¹ =
  tset-map
    (λ { (p , a) → a })

-- Multiplication

μ : ∀ {A τ₁ τ₂} → ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A) →ᵗ ⟨ τ₁ + τ₂ ⟩ᵒ A
μ {A} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , q , a) → n≤k⇒m≤k∸n⇒n+m≤k τ₁ τ₂ t p q ,
                           monotone A (≤-reflexive (n∸m∸k≡n∸m+k t τ₁ τ₂)) a })

μ⁻¹ : ∀ {A τ₁ τ₂} → ⟨ τ₁ + τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A)
μ⁻¹ {A} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , a) → m+n≤o⇒m≤o τ₁ p ,
                       n+m≤k⇒m≤k∸n τ₁ τ₂ t p ,
                       monotone A (≤-reflexive (sym (n∸m∸k≡n∸m+k t τ₁ τ₂))) a })

-- Costrength

⟨⟩-costr : ∀ {A B τ} → ⟨ τ ⟩ᵒ (A ×ᵗ B) →ᵗ ⟨ τ ⟩ᵒ A ×ᵗ B
⟨⟩-costr {B = B} {τ = τ} =
  tset-map (λ { {t} (p , x , y) → (p , x) , monotone B (m∸n≤m t τ) y })

-- Strength (for constant time-varying sets)

⟨⟩-str : ∀ {A B τ} → ⟨ τ ⟩ᵒ A ×ᵗ ConstTSet B →ᵗ ⟨ τ ⟩ᵒ (A ×ᵗ ConstTSet B)
⟨⟩-str = tset-map (λ { ((p , x) , y) → p , x , y })

-- PROPERTIES

-- ...
