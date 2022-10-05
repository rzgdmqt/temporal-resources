-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.unbox-eta (Mod : Model) where

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod
open import Semantics.Renamings.Properties.-ᶜ-wk-ren-decompose Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

unbox-eta-sound : ∀ {Γ A C τ}
                → (p : τ ≤ ctx-time Γ)
                → (V : Γ -ᶜ τ ⊢V⦂ [ τ ] A)
                → (M : Γ ∷ [ τ ] A ⊢C⦂ C)
                → ⟦ M [ Hd ↦ V-rename (-ᶜ-wk-ren τ) V ]c ⟧ᶜᵗ
                ≡ ⟦ unbox p V (C-rename (exch-ren ∘ʳ wk-ren) M [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c) ⟧ᶜᵗ

unbox-eta-sound {Γ} {A} {C} {τ} p V M = 
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
  ≡⟨ ∘ᵐ-congʳ (trans (trans (trans
      (cong₂ ⟨_,_⟩ᵐ
        (sym (
          begin
               ((fstᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ)
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                             ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                          ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ
            ,
               sndᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                    ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ ⟩ᵐ
          ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) ⟩
               (fstᵐ ∘ᵐ fstᵐ)
            ∘ᵐ idᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                    ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
               (fstᵐ ∘ᵐ fstᵐ)
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                    ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ
          ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) ⟩
               fstᵐ
            ∘ᵐ idᵐ
            ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
               fstᵐ
            ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
          ≡⟨ ⟨⟩ᵐ-fstᵐ _ _ ⟩
            idᵐ
          ∎))
        (sym (
          begin
               sndᵐ
            ∘ᵐ ⟨    idᵐ
                 ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                         ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                      ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ
            ,
               sndᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                    ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ ⟩ᵐ
          ≡⟨ ⟨⟩ᵐ-sndᵐ _ _ ⟩
               sndᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ,
                    ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ⟩ᵐ 
          ≡⟨ ⟨⟩ᵐ-sndᵐ _ _ ⟩
               ([ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
            ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
          ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
               [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
            ∘ᵐ η⊣
            ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
          ≡⟨ trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _) ⟩
               [ τ ]ᶠ ε-⟨⟩
            ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ sndᵐ)
            ∘ᵐ η⊣
            ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (η⊣-nat _)) (∘ᵐ-assoc _ _ _))) ⟩
               [ τ ]ᶠ ε-⟨⟩
            ∘ᵐ η⊣
            ∘ᵐ sndᵐ
            ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) ⟩
               [ τ ]ᶠ ε-⟨⟩
            ∘ᵐ η⊣
            ∘ᵐ ε⊣
            ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨⟩
               [ τ ]ᶠ (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
            ∘ᵐ η⊣
            ∘ᵐ ε⊣
            ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _) ⟩
               [ τ ]ᶠ η⁻¹
            ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
            ∘ᵐ η⊣
            ∘ᵐ ε⊣
            ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
               (  [ τ ]ᶠ η⁻¹
               ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
               ∘ᵐ η⊣
               ∘ᵐ ε⊣)
            ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ ∘ᵐ-congˡ (
              begin
                   [ τ ]ᶠ η⁻¹
                ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                ∘ᵐ η⊣
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)))) ⟩
                   [ τ ]ᶠ η⁻¹
                ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                ∘ᵐ η⊣
                ∘ᵐ idᵐ
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym
                  (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-η⁻¹∘η≡id))))) ⟩
                   [ τ ]ᶠ η⁻¹
                ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                ∘ᵐ η⊣
                ∘ᵐ η⁻¹
                ∘ᵐ η
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))))) ⟩
                   [ τ ]ᶠ η⁻¹
                ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                ∘ᵐ η⊣
                ∘ᵐ η⁻¹
                ∘ᵐ idᵐ
                ∘ᵐ η
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym
                  (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ []-ε∘ε⁻¹≡id)))))) ⟩
                   [ τ ]ᶠ η⁻¹
                ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                ∘ᵐ η⊣
                ∘ᵐ η⁻¹
                ∘ᵐ ε
                ∘ᵐ ε⁻¹
                ∘ᵐ η
                ∘ᵐ ε⊣
              ≡⟨ sym (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (sym η⊣-η-ε))
                  (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
                   [ τ ]ᶠ η⁻¹
                ∘ᵐ []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ η
                ∘ᵐ ε⊣
              ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ ([]-≤-nat _ _)) (∘ᵐ-assoc _ _ _)) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ η⁻¹
                ∘ᵐ ε⁻¹
                ∘ᵐ η
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ ([]-ε⁻¹-nat _)) (∘ᵐ-assoc _ _ _))) ⟩
                   []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ η⁻¹
                ∘ᵐ η
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-η⁻¹∘η≡id))) ⟩
                   []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ idᵐ
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) ⟩
                   []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
                   []-≤ z≤n
                ∘ᵐ idᵐ
                ∘ᵐ ε⁻¹
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-η⁻¹∘η≡id))) ⟩
                   []-≤ z≤n
                ∘ᵐ η⁻¹
                ∘ᵐ η
                ∘ᵐ ε⁻¹
                ∘ᵐ ε⊣
              ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
                   η⁻¹
                ∘ᵐ ⟨ 0 ⟩ᶠ ([]-≤ z≤n)
                ∘ᵐ η
                ∘ᵐ ε⁻¹
                ∘ᵐ ε⊣
              ≡⟨ ∘ᵐ-congʳ ε⊣-η-ε ⟩
                   η⁻¹
                ∘ᵐ ⟨⟩-≤ z≤n
              ∎) ⟩
               (   η⁻¹
                ∘ᵐ ⟨⟩-≤ z≤n)
            ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
               η⁻¹
            ∘ᵐ ⟨⟩-≤ z≤n
            ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-≤-nat _ _))) (∘ᵐ-assoc _ _ _))) ⟩
               η⁻¹
            ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
            ∘ᵐ ⟨⟩-≤ z≤n
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-η⁻¹-nat _))) (∘ᵐ-assoc _ _ _)) ⟩
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ η⁻¹
            ∘ᵐ ⟨⟩-≤ z≤n
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨⟩
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ ε-⟨⟩
            ∘ᵐ env-⟨⟩-ᶜ τ p
          ≡⟨ ∘ᵐ-congʳ (sym (⟦-ᶜ-wk-ren⟧≡ε∘env-⟨⟩-ᶜ p)) ⟩
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ ⟦ -ᶜ-wk-ren τ ⟧ʳ
          ∎))) (⟨⟩ᵐ-∘ᵐ _ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _))) (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ (fstᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ idᵐ ,_⟩ᵐ (sym (∘ᵐ-identityˡ _))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ (fstᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ
      (∘ᵐ-congˡ (∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _))))
      (sym (∘ᵐ-identityˡ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ idᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟦ M ⟧ᶜᵗ
        ∘ᵐ (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ ⟨ idᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ))
    ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
               ∘ᵐ ⟨ idᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ))
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (sym (⟨⟩ᵐ-sndᵐ _ _)))))) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ (⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ))
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)))) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ (⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
           ∘ᵐ idᵐ)
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _))))) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ (⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
           ∘ᵐ fstᵐ
           ∘ᵐ ⟨ idᵐ ,
                   (sndᵐ ∘ᵐ fstᵐ)
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))) ⟩
       (  (   ⟦ M ⟧ᶜᵗ
           ∘ᵐ ((⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ
                ⟨ idᵐ ,
                     sndᵐ
                  ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ)
           ∘ᵐ ⟨ idᵐ ,
                   (sndᵐ ∘ᵐ fstᵐ)
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
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
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
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
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
       ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (sym (C-rename≡∘ᵐ _ M))) ⟩
       (  ⟦ C-rename ((var-ren (Tl-∷ Hd) ∘ʳ
              cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
             ∘ʳ wk-ren) M ⟧ᶜᵗ
       ∘ᵐ idᵐ
       ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
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
