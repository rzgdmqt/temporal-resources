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

    ⟨_⟩ᵒ : Time → TSet → TSet
    ⟨_⟩ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → ⟨ τ ⟩ᵒ A →ᵗ ⟨ τ ⟩ᵒ B

    -- (Contravariant) monotonicity for gradings

    ⟨⟩-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → ⟨ τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ A

    -- Unit (and its inverse)

    η : ∀ {A} → A →ᵗ ⟨ 0 ⟩ᵒ A
    η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵗ A

    -- Multiplication (and its inverse)

    μ : ∀ {A τ₁ τ₂} → ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A) →ᵗ ⟨ τ₁ + τ₂ ⟩ᵒ A
    μ⁻¹ : ∀ {A τ₁ τ₂} → ⟨ τ₁ + τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A)

    -- PROPERTIES

    -- ⟨_⟩ is functorial

    ⟨⟩-idᵗ : ∀ {A τ} → ⟨ τ ⟩ᶠ (idᵗ {A = A}) ≡ᵗ idᵗ
    ⟨⟩-∘ᵗ : ∀ {A B C τ} → (g : B →ᵗ C) → (f : A →ᵗ B)
          → ⟨ τ ⟩ᶠ (g ∘ᵗ f) ≡ᵗ ⟨ τ ⟩ᶠ g ∘ᵗ ⟨ τ ⟩ᶠ f

    ⟨⟩-cong : ∀ {A B τ} {f g : A →ᵗ B} → f ≡ᵗ g → ⟨ τ ⟩ᶠ f ≡ᵗ ⟨ τ ⟩ᶠ g

    -- ⟨⟩-≤ is natural

    ⟨⟩-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B) → (p : τ₁ ≤ τ₂)
             → ⟨ τ₁ ⟩ᶠ f ∘ᵗ ⟨⟩-≤ {A = A} p ≡ᵗ ⟨⟩-≤ {A = B} p ∘ᵗ ⟨ τ₂ ⟩ᶠ f

    -- ⟨_⟩ is functorial in the gradings
  
    ⟨⟩-≤-refl : ∀ {A τ} → ⟨⟩-≤ {A} (≤-refl {τ}) ≡ᵗ idᵗ
    ⟨⟩-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
               → ⟨⟩-≤ {A} p ∘ᵗ ⟨⟩-≤ {A} q ≡ᵗ ⟨⟩-≤ {A} (≤-trans p q)

    ⟨⟩-≤-cong : ∀ {A τ τ'} → (p q : τ ≤ τ') → ⟨⟩-≤ {A} p ≡ᵗ ⟨⟩-≤ {A} q

    -- η and η⁻¹ are natural

    ⟨⟩-η-nat : ∀ {A B} → (f : A →ᵗ B) → ⟨ 0 ⟩ᶠ f ∘ᵗ η ≡ᵗ η ∘ᵗ f
    ⟨⟩-η⁻¹-nat : ∀ {A B} → (f : A →ᵗ B) → f ∘ᵗ η⁻¹ ≡ᵗ η⁻¹ ∘ᵗ ⟨ 0 ⟩ᶠ f

    -- μ and μ⁻¹ are natural

    ⟨⟩-μ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
             → ⟨ τ₁ + τ₂ ⟩ᶠ f ∘ᵗ μ {A} ≡ᵗ μ {B} ∘ᵗ ⟨ τ₁ ⟩ᶠ (⟨ τ₂ ⟩ᶠ f)
    ⟨⟩-μ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
               → ⟨ τ₁ ⟩ᶠ (⟨ τ₂ ⟩ᶠ f) ∘ᵗ μ⁻¹ {A} ≡ᵗ μ⁻¹ {B} ∘ᵗ ⟨ τ₁ + τ₂ ⟩ᶠ f

    ⟨⟩-μ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
           → ⟨⟩-≤ {A} (+-mono-≤ p q) ∘ᵗ μ {A} ≡ᵗ μ {A} ∘ᵗ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ {A} q) ∘ᵗ ⟨⟩-≤ {⟨ τ₂' ⟩ᵒ A} p

    -- TODO: derive the ones below from ⟨⟩-μ-≤

    ⟨⟩-μ-≤₁ : ∀ {A τ₁ τ₂ τ₁'} → (p : τ₁ ≤ τ₁')
            → ⟨⟩-≤ {A} (+-monoˡ-≤ τ₂ p) ∘ᵗ μ {A} ≡ᵗ μ {A} ∘ᵗ ⟨⟩-≤ {⟨ τ₂ ⟩ᵒ A} p
    ⟨⟩-μ-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
            → ⟨⟩-≤ {A} (+-monoʳ-≤ τ₁ q) ∘ᵗ μ {A} ≡ᵗ μ {A} ∘ᵗ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ {A} q)

    ⟨⟩-μ⁻¹-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
              → μ⁻¹ {A} ∘ᵗ ⟨⟩-≤ {A} (+-monoʳ-≤ τ₁ q) ≡ᵗ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ {A} q) ∘ᵗ μ⁻¹ {A}

    -- η is invertible

    ⟨⟩-η∘η⁻¹≡id : ∀ {A} → η {A} ∘ᵗ η⁻¹ ≡ᵗ idᵗ
    ⟨⟩-η⁻¹∘η≡id : ∀ {A} → η⁻¹ {A} ∘ᵗ η ≡ᵗ idᵗ

    -- μ is invertible

    ⟨⟩-μ∘μ⁻¹≡id : ∀ {A τ₁ τ₂} → μ {A} {τ₁} {τ₂} ∘ᵗ μ⁻¹ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
    ⟨⟩-μ⁻¹∘μ≡id : ∀ {A τ₁ τ₂} → μ⁻¹ {A} {τ₁} {τ₂} ∘ᵗ μ {A} {τ₁} {τ₂} ≡ᵗ idᵗ

    -- Graded monad laws

    ⟨⟩-μ∘η≡id : ∀ {A τ} → μ {A} {0} {τ} ∘ᵗ η {⟨ τ ⟩ᵒ A} ≡ᵗ idᵗ
    ⟨⟩-μ∘Tη≡id : ∀ {A τ} → μ {A} {τ} {0} ∘ᵗ ⟨ τ ⟩ᶠ (η {A}) ≡ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-identityʳ τ))
    ⟨⟩-μ∘μ≡≤∘μ∘Tμ : ∀ {A τ₁ τ₂ τ₃}
                  → μ {A} {τ₁ + τ₂} {τ₃} ∘ᵗ μ {⟨ τ₃ ⟩ᵒ A} {τ₁} {τ₂}
                 ≡ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃)) ∘ᵗ μ {A} {τ₁} {τ₂ + τ₃} ∘ᵗ ⟨ τ₁ ⟩ᶠ (μ {A} {τ₂} {τ₃})

    -- Graded monad laws (for inverses) (TODO: derive from above)

    ⟨⟩-Tη⁻¹∘ᵗμ⁻¹≡id : ∀ {A τ} →  ⟨ τ ⟩ᶠ (η⁻¹ {A}) ∘ᵗ μ⁻¹ {A} {τ} {0} ≡ᵗ ⟨⟩-≤ {A} (≤-reflexive (sym (+-identityʳ _)))

  -- DERIVED STRUCTURE

  ε-⟨⟩ : ∀ {A τ} → ⟨ τ ⟩ᵒ A →ᵗ A
  ε-⟨⟩ {A} {τ} = η⁻¹ ∘ᵗ ⟨⟩-≤ {A = A} z≤n
