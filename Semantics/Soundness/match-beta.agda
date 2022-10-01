-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.match-beta (Mod : Model) where

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

match-beta-sound : ∀ {Γ A B C}
                 → (V : Γ ⊢V⦂ A)
                 → (W : Γ ⊢V⦂ B)
                 → (M : Γ ∷ A ∷ B ⊢C⦂ C)
                 → ⟦ match ⦉ V , W ⦊ `in M ⟧ᶜᵗ
                 ≡ ⟦ (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟧ᶜᵗ

match-beta-sound {Γ} {A} {B} {C} V W M =
  begin
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        (trans (∘ᵐ-identityˡ _) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (⟨⟩ᵐ-fstᵐ _ _)
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))))))
        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-identityʳ _)
          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _))))))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ idᵐ ,_⟩ᵐ (sym (V-rename≡∘ᵐ wk-ren W)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (wk-ren {A = A}) W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (wk-ren {A = A}) W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (wk-ren {A = A}) W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       (⟦ M ⟧ᶜᵗ ∘ᵐ idᵐ ∘ᵐ ⟨ idᵐ , ⟦ V-rename (wk-ren {A = A}) W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (C-subst≡∘ᵐ M Hd (V-rename wk-ren W))) ⟩
       ⟦ M [ Hd ↦ V-rename wk-ren W ]c ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟦ M [ Hd ↦ V-rename wk-ren W ]c ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       ⟦ M [ Hd ↦ V-rename wk-ren W ]c ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ sym (C-subst≡∘ᵐ (M [ Hd ↦ V-rename wk-ren W ]c) Hd V) ⟩
    ⟦ (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟧ᶜᵗ
  ∎
  
