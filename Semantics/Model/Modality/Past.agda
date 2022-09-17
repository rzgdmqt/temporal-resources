-------------------------------------------------------------------
-- Semantics of the past modality `Γ ⟨ t ⟩` as a strong monoidal --
-- functor indexed by (ℕ,≥). It is the analogue of the monadic   --
-- ◆-modality on contexts in Fitch-style modal lambda calculi.   --
--                                                               --
-- Note: While `Γ ⟨ t ⟩` is a strong monoidal functor, below we  --
-- use the terminology (unit, multiplication) of graded monads.  --
-------------------------------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.Modality.Past (Cat : Category) where

open import Util.Equality
open import Util.Time

open Category Cat

record Past : Set₁ where

  field

    -- STRUCTURE

    -- Functor

    ⟨_⟩ᵒ : Time → Obj → Obj
    ⟨_⟩ᶠ : ∀ {A B} → (τ : Time) → A →ᵐ B → ⟨ τ ⟩ᵒ A →ᵐ ⟨ τ ⟩ᵒ B

    -- (Contravariant) monotonicity for gradings

    ⟨⟩-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → ⟨ τ₂ ⟩ᵒ A →ᵐ ⟨ τ₁ ⟩ᵒ A

    -- Unit (and its inverse)

    η : ∀ {A} → A →ᵐ ⟨ 0 ⟩ᵒ A
    η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵐ A

    -- Multiplication (and its inverse)

    μ : ∀ {A τ₁ τ₂} → ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A) →ᵐ ⟨ τ₁ + τ₂ ⟩ᵒ A
    μ⁻¹ : ∀ {A τ₁ τ₂} → ⟨ τ₁ + τ₂ ⟩ᵒ A →ᵐ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A)

    -- PROPERTIES

    -- ⟨_⟩ is functorial

    ⟨⟩-idᵐ : ∀ {A τ} → ⟨ τ ⟩ᶠ (idᵐ {A = A}) ≡ idᵐ
    ⟨⟩-∘ᵐ : ∀ {A B C τ} → (g : B →ᵐ C) → (f : A →ᵐ B)
          → ⟨ τ ⟩ᶠ (g ∘ᵐ f) ≡ ⟨ τ ⟩ᶠ g ∘ᵐ ⟨ τ ⟩ᶠ f

    -- ⟨⟩-≤ is natural

    ⟨⟩-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵐ B) → (p : τ₁ ≤ τ₂)
             → ⟨ τ₁ ⟩ᶠ f ∘ᵐ ⟨⟩-≤ p ≡ ⟨⟩-≤ p ∘ᵐ ⟨ τ₂ ⟩ᶠ f

    -- ⟨_⟩ is functorial in the gradings
  
    ⟨⟩-≤-refl : ∀ {A τ} → ⟨⟩-≤ {A} (≤-refl {τ}) ≡ idᵐ
    ⟨⟩-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
               → ⟨⟩-≤ {A} p ∘ᵐ ⟨⟩-≤ q ≡ ⟨⟩-≤ (≤-trans p q)

    -- η and η⁻¹ are natural

    ⟨⟩-η-nat : ∀ {A B} → (f : A →ᵐ B) → ⟨ 0 ⟩ᶠ f ∘ᵐ η ≡ η ∘ᵐ f
    ⟨⟩-η⁻¹-nat : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ η⁻¹ ≡ η⁻¹ ∘ᵐ ⟨ 0 ⟩ᶠ f

    -- μ and μ⁻¹ are natural

    ⟨⟩-μ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵐ B)
             → ⟨ τ₁ + τ₂ ⟩ᶠ f ∘ᵐ μ ≡ μ ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨ τ₂ ⟩ᶠ f)
    ⟨⟩-μ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵐ B)
               → ⟨ τ₁ ⟩ᶠ (⟨ τ₂ ⟩ᶠ f) ∘ᵐ μ⁻¹ ≡ μ⁻¹ ∘ᵐ ⟨ τ₁ + τ₂ ⟩ᶠ f

    ⟨⟩-μ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
           → ⟨⟩-≤ {A} (+-mono-≤ p q) ∘ᵐ μ ≡ μ ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q) ∘ᵐ ⟨⟩-≤ p

    -- TODO: derive the ones below from ⟨⟩-μ-≤

    ⟨⟩-μ-≤₁ : ∀ {A τ₁ τ₂ τ₁'} → (p : τ₁ ≤ τ₁')
            → ⟨⟩-≤ {A} (+-monoˡ-≤ τ₂ p) ∘ᵐ μ ≡ μ ∘ᵐ ⟨⟩-≤ p
    ⟨⟩-μ-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
            → ⟨⟩-≤ {A} (+-monoʳ-≤ τ₁ q) ∘ᵐ μ ≡ μ ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)

    ⟨⟩-μ⁻¹-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
              → μ⁻¹ {A} ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ τ₁ q) ≡ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q) ∘ᵐ μ⁻¹

    -- η is invertible

    ⟨⟩-η∘η⁻¹≡id : ∀ {A} → η {A} ∘ᵐ η⁻¹ ≡ idᵐ
    ⟨⟩-η⁻¹∘η≡id : ∀ {A} → η⁻¹ {A} ∘ᵐ η ≡ idᵐ

    -- μ is invertible

    ⟨⟩-μ∘μ⁻¹≡id : ∀ {A τ₁ τ₂} → μ {A} {τ₁} {τ₂} ∘ᵐ μ⁻¹ ≡ idᵐ
    ⟨⟩-μ⁻¹∘μ≡id : ∀ {A τ₁ τ₂} → μ⁻¹ {A} {τ₁} {τ₂} ∘ᵐ μ ≡ idᵐ

    -- Graded monad laws

    ⟨⟩-μ∘η≡id : ∀ {A τ} → μ {A} {0} {τ} ∘ᵐ η {⟨ τ ⟩ᵒ A} ≡ idᵐ
    ⟨⟩-μ∘Tη≡id : ∀ {A τ} → μ {A} {τ} {0} ∘ᵐ ⟨ τ ⟩ᶠ (η {A}) ≡ ⟨⟩-≤ (≤-reflexive (+-identityʳ τ))
    ⟨⟩-μ∘μ≡μ∘Tμ : ∀ {A τ₁ τ₂ τ₃}
                  → μ {A} ∘ᵐ μ ≡ ⟨⟩-≤ (≤-reflexive (+-assoc τ₁ τ₂ τ₃)) ∘ᵐ μ ∘ᵐ ⟨ τ₁ ⟩ᶠ μ

    -- Graded monad laws (for inverses) (TODO: derive from above)

    --⟨⟩-Tη⁻¹∘μ⁻¹≡id : ∀ {A τ} →  ⟨ τ ⟩ᶠ (η⁻¹ {A}) ∘ᵐ μ⁻¹ {A} {τ} {0} ≡ ⟨⟩-≤ {A} (≤-reflexive (sym (+-identityʳ _)))
