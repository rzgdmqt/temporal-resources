-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.box-unbox-eta (Mod : Model) where

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
open import Util.Operations
open import Util.Time

open Model Mod

box-unbox-eta-sound : ∀ {Γ A C τ}
                    → (p : τ ≤ ctx-time Γ)
                    → (V : Γ -ᶜ τ ⊢V⦂ [ τ ] A)
                    → (M : Γ ∷ [ τ ] A ⊢C⦂ C)
                    → ⟦ M [ Hd ↦ V-rename (-ᶜ-wk-ren τ) V ]c ⟧ᶜᵗ
                    ≡ ⟦ unbox p V (C-rename (exch-ren ∘ʳ wk-ren) M [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c) ⟧ᶜᵗ

box-unbox-eta-sound {Γ} {A} {C} {τ} p V M = 
  begin
    ⟦ M [ Hd ↦ V-rename (-ᶜ-wk-ren τ) V ]c ⟧ᶜᵗ
  ≡⟨ C-subst≡∘ᵐ M Hd (V-rename (-ᶜ-wk-ren τ) V) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (-ᶜ-wk-ren τ) V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (-ᶜ-wk-ren τ) V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityʳ _) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V-rename (-ᶜ-wk-ren τ) V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (V-rename≡∘ᵐ (-ᶜ-wk-ren τ) V)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ -ᶜ-wk-ren τ ⟧ʳ ⟩ᵐ
  ≡⟨ {!!} ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ ((⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ)
           ∘ᵐ ⟨ idᵐ ,
                   (sndᵐ ∘ᵐ fstᵐ)
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))))) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ fstᵐ
           ∘ᵐ ⟨ (⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ
                ,
                idᵐ ∘ᵐ sndᵐ ⟩ᵐ
           ∘ᵐ ⟨ idᵐ ,
                   (sndᵐ ∘ᵐ fstᵐ)
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _)))) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ fstᵐ
           ∘ᵐ ⟨ (⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ
                ,
                idᵐ ∘ᵐ sndᵐ ⟩ᵐ
           ∘ᵐ ⟨ idᵐ ,
                   (sndᵐ ∘ᵐ fstᵐ)
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
       ∘ᵐ idᵐ
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
       ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (sym (C-rename≡∘ᵐ _ M))) ⟩
       (  ⟦ C-rename ((var-ren (Tl-∷ Hd) ∘ʳ
              cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
             ∘ʳ wk-ren) M ⟧ᶜᵗ
       ∘ᵐ idᵐ
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
       ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym
      (C-subst≡∘ᵐ
        (C-rename ((var-ren (Tl-∷ Hd) ∘ʳ
           cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
          ∘ʳ wk-ren) M)
        Hd (box (var (Tl-⟨⟩ Hd))))) ⟩
       ⟦ C-rename ((var-ren (Tl-∷ Hd) ∘ʳ
           cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
          ∘ʳ wk-ren) M [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ∎
