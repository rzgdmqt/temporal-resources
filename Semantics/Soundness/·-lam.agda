-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.·-lam (Mod : Model) where

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

·-lam-sound : ∀ {Γ A C}
            → (M : Γ ∷ A ⊢C⦂ C)
            → (W : Γ ⊢V⦂ A)
            → ⟦ lam M · W ⟧ᶜᵗ ≡ ⟦ M [ Hd ↦ W ]c ⟧ᶜᵗ

·-lam-sound {Γ} {A} {C} M W = 
  begin
       uncurryᵐ idᵐ
    ∘ᵐ ⟨ curryᵐ ⟦ M ⟧ᶜᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (cong₂ ⟨_,_⟩ᵐ
      (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityʳ _))))
      (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _))))) (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
       uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ (curryᵐ ⟦ M ⟧ᶜᵗ) idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _))) ⟩
       uncurryᵐ (idᵐ ∘ᵐ (curryᵐ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-identityˡ _)) ⟩
       uncurryᵐ (curryᵐ ⟦ M ⟧ᶜᵗ)
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityʳ _))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ split-env⁻¹ {Γ = Γ ∷ A} split-[]
    ∘ᵐ ⟦ [] ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ = Γ} split-[]
  ≡⟨ sym (C-subst≡∘ᵐ M Hd W) ⟩
    ⟦ M [ Hd ↦ W ]c ⟧ᶜᵗ
  ∎
