-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.;-return (Mod : Model) where

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

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

;-return-soundness : ∀ {Γ A B τ}
                   → (V : Γ ⊢V⦂ A)
                   → (M : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ)
                   → ⟦ return V ; M ⟧ᶜᵗ
                   ≡ ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) M [ Hd ↦ V ]c ⟧ᶜᵗ

;-return-soundness {Γ} {A} {B} V M =
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ M ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ {!!} ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟦ cong-∷-ren {Γ' = Γ} {A = A} ⟨⟩-η-ren ⟧ʳ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ cong-∷-ren {Γ' = Γ} {A = A} ⟨⟩-η-ren ⟧ʳ)
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (C-rename≡∘ᵐ (cong-∷-ren ⟨⟩-η-ren) M)) ⟩
       ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ sym (C-subst≡∘ᵐ (C-rename (cong-∷-ren ⟨⟩-η-ren) M) Hd V) ⟩
    ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) M [ Hd ↦ V ]c ⟧ᶜᵗ
  ∎

