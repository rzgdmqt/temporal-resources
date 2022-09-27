-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.unbox-box (Mod : Model) where

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod
open import Semantics.Renamings.Properties.-ᶜ-⟨⟩-ren-decompose Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

unbox-box-sound : ∀ {Γ A C τ}
                → (p : τ ≤ ctx-time Γ)
                → (V : (Γ -ᶜ τ) ⟨ τ ⟩ ⊢V⦂ A)
                → (N : Γ ∷ A ⊢C⦂ C)
                → ⟦ unbox p (box V) N ⟧ᶜᵗ
                ≡ ⟦ N [ Hd ↦ V-rename (-ᶜ-⟨⟩-ren τ p) V ]c ⟧ᶜᵗ

unbox-box-sound {Γ} {A} {C} {τ} p V N = 
  begin
       ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ε⊣
         ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣)
         ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
       ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ε⊣
         ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ)
         ∘ᵐ ⟨ τ ⟩ᶠ η⊣
         ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (trans (sym (∘ᵐ-assoc _ _ _))
      (trans (∘ᵐ-congˡ (sym (ε⊣-nat _))) (∘ᵐ-assoc _ _ _)))) ⟩
       ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ⟦ V ⟧ᵛᵗ
         ∘ᵐ ε⊣
         ∘ᵐ ⟨ τ ⟩ᶠ η⊣
         ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ε⊣∘Fη⊣≡id)))) ⟩
       ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ⟦ V ⟧ᵛᵗ
         ∘ᵐ idᵐ
         ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ ((cong ⟨ idᵐ ,_⟩ᵐ) (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) ⟩
      ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ⟦ V ⟧ᵛᵗ
         ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congʳ (sym (⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ p)))) ⟩
      ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ⟦ V ⟧ᵛᵗ
         ∘ᵐ ⟦ -ᶜ-⟨⟩-ren τ p ⟧ʳ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (sym (V-rename≡∘ᵐ (-ᶜ-⟨⟩-ren τ p) V ))) ⟩
      ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (-ᶜ-⟨⟩-ren τ p) V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
      ⟦ N ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (-ᶜ-⟨⟩-ren τ p) V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
      ⟦ N ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (-ᶜ-⟨⟩-ren τ p) V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ sym (C-subst≡∘ᵐ N Hd (V-rename (-ᶜ-⟨⟩-ren τ p) V)) ⟩
    ⟦ N [ Hd ↦ V-rename (-ᶜ-⟨⟩-ren τ p) V ]c ⟧ᶜᵗ
  ∎
