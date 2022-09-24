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

⟨⟩-η⁻¹∘μ⁻¹≡id : ∀ {A τ} → η⁻¹ ∘ᵐ μ⁻¹ {A} {0} {τ} ≡ idᵐ
⟨⟩-η⁻¹∘μ⁻¹≡id = 
  begin
       η⁻¹
    ∘ᵐ μ⁻¹
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id) ⟩
       (   μ
        ∘ᵐ η)
    ∘ᵐ η⁻¹
    ∘ᵐ μ⁻¹
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
       μ
    ∘ᵐ (   η
        ∘ᵐ η⁻¹)
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-η∘η⁻¹≡id) ⟩
       μ
    ∘ᵐ idᵐ
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       μ
    ∘ᵐ μ⁻¹
  ≡⟨ ⟨⟩-μ∘μ⁻¹≡id ⟩
    idᵐ
  ∎

-- Other, mixed laws

⟨⟩-Tμ∘μ⁻¹≡μ⁻¹∘μ : ∀ {A τ₁ τ₂ τ₃}
                → ⟨ τ₁ ⟩ᶠ μ ∘ᵐ μ⁻¹ {⟨ τ₃ ⟩ᵒ A} {τ₁} {τ₂}
                ≡ μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc τ₁ τ₂ τ₃))) ∘ᵐ μ
⟨⟩-Tμ∘μ⁻¹≡μ⁻¹∘μ {A} {τ₁} {τ₂} {τ₃} = 
  begin
       ⟨ τ₁ ⟩ᶠ μ
    ∘ᵐ μ⁻¹
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ μ
    ∘ᵐ μ⁻¹   
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-μ⁻¹∘μ≡id)) ⟩
       μ⁻¹
    ∘ᵐ μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ μ
    ∘ᵐ μ⁻¹   
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       μ⁻¹
    ∘ᵐ idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ μ
    ∘ᵐ μ⁻¹   
  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
      (trans (⟨⟩-≤-trans _ _) (trans (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟨⟩-≤-refl))))) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc τ₁ τ₂ τ₃)))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-assoc τ₁ τ₂ τ₃))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ μ
    ∘ᵐ μ⁻¹   
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ ⟨⟩-μ∘μ≡μ∘Tμ)
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc τ₁ τ₂ τ₃)))
    ∘ᵐ μ
    ∘ᵐ μ {⟨ τ₃ ⟩ᵒ A} {τ₁} {τ₂}
    ∘ᵐ μ⁻¹   
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ ⟨⟩-μ∘μ⁻¹≡id)) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc τ₁ τ₂ τ₃)))
    ∘ᵐ μ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc τ₁ τ₂ τ₃)))
    ∘ᵐ μ
  ∎

{-
   {⟨ τ₁ + τ₂ ⟩ᵒ (⟨ τ₃ ⟩ᵒ A) →ᵐ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ + τ₃ ⟩ᵒ A)}
-}
