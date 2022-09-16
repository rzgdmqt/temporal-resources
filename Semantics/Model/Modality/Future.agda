------------------------------------------------------------------------
-- Semantics of the future modality `[ t ] A` as a strong monoidal    --
-- functor indexed by (ℕ,≤). It is the analogue of the comonadic      --
-- □-modality on types/formulae in Fitch-style modal lambda calculi.  --
--                                                                    --
-- Note: While `[ t ] A` is a strong monoidal functor, then below we  --
-- use the terminology (counit, comultiplication) of graded comonads. --
------------------------------------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.Modality.Future (Cat : Category) where

open import Util.Time

open Category Cat

record Future : Set₁ where

  field

    -- STRUCTURE

    -- Functor
    
    [_]ᵒ : Time → TSet → TSet
    [_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → [ τ ]ᵒ A →ᵗ [ τ ]ᵒ B
    
    -- Monotonicity for gradings

    []-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵗ [ τ₂ ]ᵒ A
  
    -- Counit and its inverse

    ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
    ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A

    -- Comultiplication and its inverse
    
    δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵗ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
    δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵗ [ τ₁ + τ₂ ]ᵒ A

    -- PROPERTIES

    -- [_] is functorial

    []-idᵗ : ∀ {A τ} → [ τ ]ᶠ (idᵗ {A = A}) ≡ᵗ idᵗ
    []-∘ᵗ : ∀ {A B C τ} → (f : A →ᵗ B) → (g : B →ᵗ C)
          → [ τ ]ᶠ (g ∘ᵗ f) ≡ᵗ [ τ ]ᶠ g ∘ᵗ [ τ ]ᶠ f

    -- []-≤ is natural

    []-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B) → (p : τ₁ ≤ τ₂)
             → [ τ₂ ]ᶠ f ∘ᵗ []-≤ {A = A} p ≡ᵗ []-≤ {A = B} p ∘ᵗ [ τ₁ ]ᶠ f

    -- [_] is functorial in the gradings

    []-≤-refl : ∀ {A τ} → []-≤ {A} (≤-refl {τ}) ≡ᵗ idᵗ
    []-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
               → []-≤ {A} q ∘ᵗ []-≤ {A} p ≡ᵗ []-≤ {A} (≤-trans p q)

    -- ε and ε⁻¹ are natural

    []-ε-nat : ∀ {A B} → (f : A →ᵗ B) → f ∘ᵗ ε ≡ᵗ ε ∘ᵗ [ 0 ]ᶠ f
    []-ε⁻¹-nat : ∀ {A B} → (f : A →ᵗ B) → [ 0 ]ᶠ f ∘ᵗ ε⁻¹ ≡ᵗ ε⁻¹ ∘ᵗ f

    -- δ and δ⁻¹ is natural

    []-δ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
             → [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f) ∘ᵗ δ {A} ≡ᵗ δ {B} ∘ᵗ [ τ₁ + τ₂ ]ᶠ f
    []-δ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
               → [ τ₁ + τ₂ ]ᶠ f ∘ᵗ δ⁻¹ {A} ≡ᵗ δ⁻¹ {B} ∘ᵗ [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f)
    []-δ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
           → [ τ₁' ]ᶠ ([]-≤ {A} q) ∘ᵗ []-≤ {[ τ₂ ]ᵒ A} p ∘ᵗ δ {A = A} ≡ᵗ δ {A} ∘ᵗ []-≤ {A} (+-mono-≤ p q)

    -- ε is invertible

    []-ε∘ε⁻¹≡id : ∀ {A} → ε {A} ∘ᵗ ε⁻¹ ≡ᵗ idᵗ
    []-ε⁻¹∘ε≡id : ∀ {A} → ε⁻¹ {A} ∘ᵗ ε ≡ᵗ idᵗ

    -- δ is invertible

    []-δ∘δ⁻¹≡id : ∀ {A τ₁ τ₂} → δ {A} {τ₁} {τ₂} ∘ᵗ δ⁻¹ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
    []-δ⁻¹∘δ≡id : ∀ {A τ₁ τ₂} → δ⁻¹ {A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁} {τ₂} ≡ᵗ idᵗ

    -- Graded comonad laws

    []-ε∘δ≡id : ∀ {A τ} → ε ∘ᵗ δ {A} {0} {τ} ≡ᵗ idᵗ
    []-Dε∘δ≡≤ : ∀ {A τ} → [ τ ]ᶠ (ε {A}) ∘ᵗ δ {A} {τ} {0} ≡ᵗ []-≤ {A} (≤-reflexive (+-identityʳ τ))
    []-δ∘δ≡Dδ∘δ∘≤ : ∀ {A τ₁ τ₂ τ₃}
                  → δ {[ τ₃ ]ᵒ A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁ + τ₂} {τ₃}
                  ≡ᵗ    [ τ₁ ]ᶠ (δ {A} {τ₂} {τ₃}) ∘ᵗ δ {A} {τ₁} {τ₂ + τ₃}
                     ∘ᵗ []-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃))

    -- [_]ᵒ is monoidal (with respect to ×ᵗ) (TODO: derive from adjunction)

    []-monoidal : ∀ {A B τ}
                → [ τ ]ᵒ A ×ᵗ [ τ ]ᵒ B →ᵗ [ τ ]ᵒ (A ×ᵗ B)

  -- DERIVED STRUCTURE

  η-[] : ∀ {A τ} → A →ᵗ [ τ ]ᵒ A
  η-[] {A} {τ} = []-≤ {A = A} z≤n ∘ᵗ ε⁻¹
