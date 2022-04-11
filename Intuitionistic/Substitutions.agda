-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language
open import ContextModality

module Substitutions where

-- Any variable in a context, also if not available now (used to
-- speak about substituting values for variables, because for
-- compositionality need to substitute under ⟨_⟩ modalities as well)

data _∈ᵃ_ (A : VType) : Ctx → Set where
  Hdᵃ    : ∀ {Γ}   → A ∈ᵃ Γ ∷ᶜ A
  Tlᵃ-∷ᶜ : ∀ {Γ B} → A ∈ᵃ Γ → A ∈ᵃ Γ ∷ᶜ B
  Tlᵃ-⟨⟩ : ∀ {Γ τ} → A ∈ᵃ Γ → A ∈ᵃ Γ ⟨ τ ⟩
  
infix 27 _∈ᵃ_

-- If a variable is in context now, it is there at any time

∈-∈ᵃ : ∀ {Γ A} → A ∈ Γ → A ∈ᵃ Γ
∈-∈ᵃ Hd     = Hdᵃ
∈-∈ᵃ (Tl x) = Tlᵃ-∷ᶜ (∈-∈ᵃ x)

-- Context split by a variable

var-split : ∀ {Γ A}
          → A ∈ᵃ Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ ∷ᶜ A , Γ₂ split Γ)

var-split {Γ ∷ᶜ A} Hdᵃ = Γ , [] , split-[]
var-split {Γ ∷ᶜ B} (Tlᵃ-∷ᶜ x) with var-split x
... | Γ₁ , Γ₂ , p = Γ₁ , Γ₂ ∷ᶜ B , split-∷ᶜ p
var-split {Γ ⟨ τ ⟩} (Tlᵃ-⟨⟩ x) with var-split x
... | Γ₁ , Γ₂ , p = Γ₁ , Γ₂ ⟨ τ ⟩ , split-⟨⟩ p

-- TODO: write up the proofs of this

-- Substituting a value for any variable in context

postulate

  _[_↦ᵃ_]v : ∀ {Γ A B}
           → Γ ⊢V⦂ B
           → (x : A ∈ᵃ Γ)
           → proj₁ (var-split x) ⊢V⦂ A
           -----------------------------------------------------------
           → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  _[_↦ᵃ_]c : ∀ {Γ A C}
           → Γ ⊢C⦂ C
           → (x : A ∈ᵃ Γ)
           → proj₁ (var-split x) ⊢V⦂ A
           -----------------------------------------------------------
           → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢C⦂ C


-- Substituting a value for variable available now

_[_↦_]v : ∀ {Γ A B}
        → Γ ⊢V⦂ B
        → (x : A ∈ Γ)
        → proj₁ (var-split (∈-∈ᵃ x)) ⊢V⦂ A
        -------------------------------------------------------------------------
        → proj₁ (var-split (∈-∈ᵃ x)) ++ᶜ proj₁ (proj₂ (var-split (∈-∈ᵃ x))) ⊢V⦂ B

V [ x ↦ W ]v = V [ ∈-∈ᵃ x ↦ᵃ W ]v

_[_↦_]c : ∀ {Γ A C}
        → Γ ⊢C⦂ C
        → (x : A ∈ Γ)
        → proj₁ (var-split (∈-∈ᵃ x)) ⊢V⦂ A
        -------------------------------------------------------------------------
        → proj₁ (var-split (∈-∈ᵃ x)) ++ᶜ proj₁ (proj₂ (var-split (∈-∈ᵃ x))) ⊢C⦂ C

M [ x ↦ W ]c = M [ ∈-∈ᵃ x ↦ᵃ W ]c
