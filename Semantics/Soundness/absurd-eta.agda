-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.absurd-eta (Mod : Model) where

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

absurd-eta-sound : ∀ {Γ C}
            → (V : Γ ⊢V⦂ Empty)
            → (M : Γ ∷ Empty ⊢C⦂ C)
            → ⟦ absurd {C = C} V ⟧ᶜᵗ ≡ ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ

absurd-eta-sound {Γ} {C} V M = 
  begin
       initialᵐ
    ∘ᵐ ⟦ V ⟧ᵛᵗ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
       initialᵐ
    ∘ᵐ sndᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ initialᵐ-unique)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ initialᵐ
    ∘ᵐ sndᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ initialᵐ
    ∘ᵐ sndᵐ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (
      trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
        (sym (⟨⟩ᵐ-unique _ _ _
          (trans (∘ᵐ-identityʳ _) (sym (⟨⟩ᵐ-sndᵐ _ _)))
          (trans (∘ᵐ-identityʳ _) (sym (⟨⟩ᵐ-fstᵐ _ _))))))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ initialᵐ
    ∘ᵐ sndᵐ
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ (   initialᵐ
        ∘ᵐ sndᵐ
        ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ)
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (curryᵐ-uncurryᵐ-iso _))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ uncurryᵐ (curryᵐ (   initialᵐ
                         ∘ᵐ sndᵐ
                         ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ))
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong uncurryᵐ initialᵐ-unique)) ⟩ -- intial objects in CCC are strict
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ uncurryᵐ initialᵐ
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong uncurryᵐ (sym initialᵐ-unique))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ uncurryᵐ (curryᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ)
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ sndᵐ , fstᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
      (∘ᵐ-congˡ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
        (sym (⟨⟩ᵐ-unique _ _ _
          (trans (∘ᵐ-identityʳ _) (sym (⟨⟩ᵐ-sndᵐ _ _)))
          (trans (∘ᵐ-identityʳ _) (sym (⟨⟩ᵐ-fstᵐ _ _)))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ sym (C-subst≡∘ᵐ M Hd V) ⟩
    ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ
  ∎
