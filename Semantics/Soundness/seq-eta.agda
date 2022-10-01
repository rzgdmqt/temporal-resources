-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.seq-eta (Mod : Model) where

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Util.Equality
open import Util.Time

open Model Mod

seq-eta-sound : ∀ {Γ A τ}
              → (M : Γ ⊢C⦂ A ‼ τ)
              → ⟦ M ⟧ᶜᵗ
              ≡ ⟦ τ-subst (+-identityʳ τ) (M ; return (var Hd)) ⟧ᶜᵗ

seq-eta-sound {Γ} {A} {τ} M =
  begin
    ⟦ M ⟧ᶜᵗ
  ≡⟨ sym (⟨⟩ᵐ-sndᵐ _ _) ⟩
       sndᵐ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ strᵀ-sndᵐ)) ⟩
       Tᶠ sndᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ Tᶠ sndᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym τ-substᵀ-refl) ⟩
       τ-substᵀ refl
    ∘ᵐ Tᶠ sndᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (cong τ-substᵀ uip) ⟩
       τ-substᵀ (trans (sym (+-identityʳ τ)) (+-identityʳ τ))
    ∘ᵐ Tᶠ sndᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (τ-substᵀ-trans _ _))) ⟩
       τ-substᵀ (+-identityʳ τ)
    ∘ᵐ τ-substᵀ (sym (+-identityʳ τ))
    ∘ᵐ Tᶠ sndᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ T-μ∘Tη≡id))) ⟩
       τ-substᵀ (+-identityʳ τ)
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ ηᵀ
    ∘ᵐ Tᶠ sndᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
       τ-substᵀ (+-identityʳ τ)
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (ηᵀ ∘ᵐ sndᵐ)
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨⟩
       τ-substᵀ (+-identityʳ τ)
    ∘ᵐ ⟦ M ; return (var Hd) ⟧ᶜᵗ
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ (+-identityʳ τ) (M ; return (var Hd))) ⟩
    ⟦ τ-subst (+-identityʳ τ) (M ; return (var Hd)) ⟧ᶜᵗ
  ∎
