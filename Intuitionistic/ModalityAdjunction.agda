---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

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
open import ContextModality
open import TypeModality

module ModalityAdjunction where

-- STRUCTURE

-- Unit of the adjunction

η⊣ : ∀ {A τ} → A →ᵗ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
η⊣ {A} {τ} =
  tset-map
    (λ {t'} a →
      m≤n+m τ t' ,
      monotone A (≤-reflexive (sym (m+n∸n≡m t' τ))) a)

-- Counit of the adjunction

ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵗ A
ε⊣ {A} {τ} =
  tset-map
    (λ { {t'} (p , a) → monotone A (n≤m⇒m∸n+n≤m τ t' p) a })


-- PROPERTIES

-- Triangle equations of the adjunction

⊣-ε∘Fη≡id : ∀ {A τ} → ε⊣ {⟨ τ ⟩ᵒ A} ∘ᵗ ⟨ τ ⟩ᶠ (η⊣ {A}) ≡ᵗ idᵗ
⊣-ε∘Fη≡id {A} {τ} x =
  cong₂ _,_
    (≤-irrelevant _ _)
    (trans
      (monotone-trans A _ _ _)
      (trans
        (cong (λ p → monotone A p (proj₂ x)) (≤-irrelevant _ _))
        (monotone-refl A (proj₂ x))))

⊣-Gε∘η≡id : ∀ {A τ} → [ τ ]ᶠ (ε⊣ {A}) ∘ᵗ η⊣ {[ τ ]ᵒ A} ≡ᵗ idᵗ
⊣-Gε∘η≡id {A} {τ} x =
  trans
    (monotone-trans A _ _ _)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

-- ...
