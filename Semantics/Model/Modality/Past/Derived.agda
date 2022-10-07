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

ε-⟨⟩-nat : ∀ {A B τ}
         → (f : A →ᵐ B)
         → f ∘ᵐ ε-⟨⟩
         ≡ ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ f
ε-⟨⟩-nat {A} {B} {τ} f =
  begin
    f ∘ᵐ η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
    η⁻¹ ∘ᵐ ⟨ 0 ⟩ᶠ f ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-≤-nat _ _) ⟩
    η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n ∘ᵐ ⟨ τ ⟩ᶠ f
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ τ ⟩ᶠ f
  ∎
 
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

-- μ and μ⁻¹ are natural

⟨⟩-μ-≤₁ : ∀ {A τ₁ τ₂ τ₁'} → (p : τ₁ ≤ τ₁')
        → ⟨⟩-≤ {A} (+-monoˡ-≤ τ₂ p) ∘ᵐ μ ≡ μ ∘ᵐ ⟨⟩-≤ p

⟨⟩-μ-≤₁ {A} {τ₁} {τ₂} {τ₁'} p = 
  begin
       ⟨⟩-≤ (+-monoˡ-≤ τ₂ p)
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤ (+-mono-≤ p ≤-refl)
    ∘ᵐ μ
  ≡⟨ ⟨⟩-μ-≤ _ _ ⟩
       μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ ≤-refl)
    ∘ᵐ ⟨⟩-≤ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ₁ ⟩ᶠ ⟨⟩-≤-refl)) ⟩
       μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ idᵐ
    ∘ᵐ ⟨⟩-≤ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-idᵐ) ⟩
       μ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨⟩-≤ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       μ
    ∘ᵐ ⟨⟩-≤ p
  ∎

⟨⟩-μ-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
        → ⟨⟩-≤ {A} (+-monoʳ-≤ τ₁ q) ∘ᵐ μ ≡ μ ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)

⟨⟩-μ-≤₂ {A} {τ₁} {τ₂} {τ₂'} q = 
  begin
       ⟨⟩-≤ (+-monoʳ-≤ τ₁ q)
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤ (+-mono-≤ ≤-refl q)
    ∘ᵐ μ
  ≡⟨ ⟨⟩-μ-≤ _ _ ⟩
       μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)
    ∘ᵐ ⟨⟩-≤ ≤-refl
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨⟩-≤-refl) ⟩
       μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityʳ _) ⟩
       μ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)
  ∎

⟨⟩-μ⁻¹-≤₁ : ∀ {A τ₁ τ₁' τ₂} → (p : τ₁ ≤ τ₁')
          → μ⁻¹ {A} ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ τ₂ p) ≡ ⟨⟩-≤ p ∘ᵐ μ⁻¹

⟨⟩-μ⁻¹-≤₁ {A} {τ₁} {τ₁'} {τ₂} p  = 
  begin
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ τ₂ p)
  ≡⟨ ∘ᵐ-congʳ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-mono-≤ p ≤-refl)
  ≡⟨ ⟨⟩-μ⁻¹-≤ _ _ ⟩
       ⟨⟩-≤ p
    ∘ᵐ ⟨ τ₁' ⟩ᶠ (⟨⟩-≤ ≤-refl)
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ₁' ⟩ᶠ ⟨⟩-≤-refl)) ⟩
       ⟨⟩-≤ p
    ∘ᵐ ⟨ τ₁' ⟩ᶠ idᵐ
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-idᵐ) ⟩
       ⟨⟩-≤ p
    ∘ᵐ idᵐ
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       ⟨⟩-≤ p
    ∘ᵐ μ⁻¹
  ∎

⟨⟩-μ⁻¹-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
          → μ⁻¹ {A} ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ τ₁ q) ≡ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q) ∘ᵐ μ⁻¹

⟨⟩-μ⁻¹-≤₂ {A} {τ₁} {τ₂} {τ₂'} q = 
  begin
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ τ₁ q)
  ≡⟨ ∘ᵐ-congʳ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-mono-≤ ≤-refl q)
  ≡⟨ ⟨⟩-μ⁻¹-≤ _ _ ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-congˡ ⟨⟩-≤-refl ⟩
       idᵐ
    ∘ᵐ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)
    ∘ᵐ μ⁻¹
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
       ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ q)
    ∘ᵐ μ⁻¹
  ∎
