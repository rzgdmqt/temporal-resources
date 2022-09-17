-------------------------------------------------------------------
-- Semantics of the past modality `Γ ⟨ t ⟩` as a strong monoidal --
-- functor indexed by (ℕ,≥). It is the analogue of the monadic   --
-- ◆-modality on contexts in Fitch-style modal lambda calculi.   --
--                                                               --
-- Note: While `Γ ⟨ t ⟩` is a strong monoidal functor, below we  --
-- use the terminology (unit, multiplication) of graded monads.  --
-------------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Past

module Semantics.Model.Modality.Past.Derived (Cat : Category)
                                             (Pas : Past Cat) where

open import Util.Equality
open import Util.Time

open Category Cat
open Past Pas

open import Semantics.Model.Category.Derived Cat

-- Counit
 
ε-⟨⟩ : ∀ {A τ} → ⟨ τ ⟩ᵒ A →ᵐ A
ε-⟨⟩ {A} {τ} = η⁻¹ ∘ᵐ ⟨⟩-≤ {A = A} z≤n
 
-- Graded monad laws (for inverses)
 
⟨⟩-Tη⁻¹∘μ⁻¹≡id : ∀ {A τ} → ⟨ τ ⟩ᶠ (η⁻¹ {A}) ∘ᵐ μ⁻¹ ≡ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
⟨⟩-Tη⁻¹∘μ⁻¹≡id {A} {τ} = 
  begin
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)) ⟩
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ μ⁻¹
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
      (sym (trans (⟨⟩-≤-trans _ _)
        (trans (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟨⟩-≤-refl))))  ⟩
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-identityʳ τ))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-μ∘Tη≡id))) ⟩
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ μ⁻¹
    ∘ᵐ (   μ {A} {τ} {0}
        ∘ᵐ ⟨ τ ⟩ᶠ (η {A}))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
      (trans (∘ᵐ-congˡ (sym (∘ᵐ-assoc _ _ _))) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ (   μ⁻¹
        ∘ᵐ μ {A} {τ} {0})
    ∘ᵐ ⟨ τ ⟩ᶠ (η {A})
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-μ⁻¹∘μ≡id) ⟩
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ (η {A})
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       ⟨ τ ⟩ᶠ η⁻¹
    ∘ᵐ ⟨ τ ⟩ᶠ (η {A})
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨ τ ⟩ᶠ η⁻¹
        ∘ᵐ ⟨ τ ⟩ᶠ (η {A}))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-congˡ (trans (sym (⟨⟩-∘ᵐ _ _)) (cong ⟨ τ ⟩ᶠ ⟨⟩-η⁻¹∘η≡id)) ⟩
       ⟨ τ ⟩ᶠ idᵐ
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-congˡ ⟨⟩-idᵐ ⟩
       idᵐ
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ τ)))
  ∎
