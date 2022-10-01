-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.seq-return (Mod : Model) where

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

open Model Mod

seq-return-sound : ∀ {Γ A B τ}
                 → (V : Γ ⊢V⦂ A)
                 → (M : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ)
                 → ⟦ return V ; M ⟧ᶜᵗ
                 ≡ ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) M [ Hd ↦ V ]c ⟧ᶜᵗ

seq-return-sound {Γ} {A} {B} V M =
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ M ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (
      begin
        ⟨ η⊣ ,
          ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
      ≡⟨ cong₂ ⟨_,_⟩ᵐ η⊣≡ε⁻¹∘η refl ⟩
        ⟨ ε⁻¹ ∘ᵐ η ,
          ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
      ≡⟨ cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _))) (∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩
        ⟨ ε⁻¹ ∘ᵐ fstᵐ ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
          ηᵀ ∘ᵐ sndᵐ ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ cong₂ ⟨_,_⟩ᵐ (sym (∘ᵐ-assoc _ _ _)) (sym (∘ᵐ-assoc _ _ _)) ⟩
        ⟨ (ε⁻¹ ∘ᵐ fstᵐ) ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
          (ηᵀ ∘ᵐ sndᵐ) ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
      ∎) (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ M ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
    ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ strᵀ-ηᵀ))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ M ⟧ᶜᵗ
    ∘ᵐ ηᵀ
    ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (ηᵀ-nat _))) (∘ᵐ-assoc _ _ _))) ⟩
       μᵀ
    ∘ᵐ ηᵀ
    ∘ᵐ ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ T-μ∘η≡id) ⟩
       idᵐ
    ∘ᵐ ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (cong₂ ⟨_,_⟩ᵐ
      (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityʳ _))))
      (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _))))) (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ η ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨⟩
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

