-----------------------------------------------------------------------------------------
-- Relating the syntactic effect information coercion to semantic morphism composition --
-----------------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Interpretation.Properties.τ-subst (Mod : Model) where

open import Syntax.Types
open import Syntax.Language
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Util.Equality

open Model Mod

⟦τ-subst⟧≡τ-substᵀ : ∀ {Γ A τ τ'}
                   → (p : τ ≡ τ')
                   → (M : Γ ⊢C⦂ A ‼ τ)
                   → ⟦ τ-subst p M ⟧ᶜᵗ
                   ≡ τ-substᵀ p ∘ᵐ ⟦ M ⟧ᶜᵗ

⟦τ-subst⟧≡τ-substᵀ refl M = 
  begin
    ⟦ M ⟧ᶜᵗ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ ⟦ M ⟧ᶜᵗ
  ≡⟨ ∘ᵐ-congˡ (sym τ-substᵀ-refl) ⟩
    τ-substᵀ refl ∘ᵐ ⟦ M ⟧ᶜᵗ
  ∎
