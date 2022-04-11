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

module Substitutions where

-- Context split by a variable

var-split : ∀ {Γ A τ}
          → A ∈[ τ ] Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ ∷ᶜ A , Γ₂ split Γ × ctx-delay Γ₂ ≡ τ)

var-split {Γ ∷ᶜ A} Hd = Γ , [] , split-[] , refl
var-split {Γ ∷ᶜ B} (Tl-∷ᶜ x) with var-split x
... | Γ₁ , Γ₂ , p , q = Γ₁ , Γ₂ ∷ᶜ B , split-∷ᶜ p , q
var-split {Γ ⟨ τ ⟩} (Tl-⟨⟩ x) with var-split x
... | Γ₁ , Γ₂ , p , q =
  Γ₁ , Γ₂ ⟨ τ ⟩ , split-⟨⟩ p , trans (cong (_+ τ) q) (+-comm _ τ)

-- Substituting a value for any variable in context

mutual

  _[_↦_]v : ∀ {Γ A B τ}
           → Γ ⊢V⦂ B
           → (x : A ∈[ τ ] Γ)
           → proj₁ (var-split x) ⊢V⦂ A
           -----------------------------------------------------------
           → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  var y   [ x ↦ W ]v = {!!}
  const c [ x ↦ W ]v = const c
  ⋆       [ x ↦ W ]v = ⋆
  lam M   [ x ↦ W ]v = lam (M [ Tl-∷ᶜ x ↦ W ]c)
  box V   [ x ↦ W ]v = box (V [ Tl-⟨⟩ x ↦ W ]v)

  _[_↦_]c : ∀ {Γ A C τ}
           → Γ ⊢C⦂ C
           → (x : A ∈[ τ ] Γ)
           → proj₁ (var-split x) ⊢V⦂ A
           -----------------------------------------------------------
           → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢C⦂ C

  return V       [ x ↦ W ]c = return (V [ x ↦ W ]v)
  (M ; N)        [ x ↦ W ]c = (M [ x ↦ W ]c) ; (N [ Tl-∷ᶜ x ↦ W ]c)
  (V₁ · V₂)      [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  absurd V       [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ᶜ (Tl-⟨⟩ x) ↦ W ]c)
  unbox p q V M  [ x ↦ W ]c = unbox {!!} {!!} {!!} (M [ Tl-∷ᶜ x ↦ W ]c)
  coerce p M     [ x ↦ W ]c = coerce p (M [ x ↦ W ]c)





{-
var-split {Γ ∷ᶜ A} Hdᵃ = Γ , [] , split-[]
var-split {Γ ∷ᶜ B} (Tl-∷ᶜ x) with var-split x
... | Γ₁ , Γ₂ , p = Γ₁ , Γ₂ ∷ᶜ B , split-∷ᶜ p
var-split {Γ ⟨ τ ⟩} (Tl-⟨⟩ x) with var-split x
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

-}
