-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.;-assoc (Mod : Model) where

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

;-assoc-sound : ∀ {Γ A B C τ τ' τ''}
              → (M : Γ ⊢C⦂ A ‼ τ)
              → (N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
              → (P : Γ ⟨ τ + τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
              → ⟦ (M ; N) ; P ⟧ᶜᵗ
              ≡ ⟦ τ-subst (sym (+-assoc τ τ' τ'')) (M ;
                    (N ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P)) ⟧ᶜᵗ

;-assoc-sound {Γ} {A} {B} {C} {τ} {τ'} {τ''} M N P = 
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ ,
            μᵀ
         ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
         ∘ᵐ strᵀ
         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           strᵀ
        ∘ᵐ ⟨ η⊣ ,
                μᵀ
             ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
             ∘ᵐ strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (trans (trans
          (cong₂ ⟨_,_⟩ᵐ
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-fstᵐ _ _)
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-congʳ
                (∘ᵐ-congˡ (∘ᵐ-identityˡ _))) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityʳ _)))))))))
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-congʳ
              (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-sndᵐ _ _) (trans (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))))))))))
          (⟨⟩ᵐ-∘ᵐ _ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _))) (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
           strᵀ
        ∘ᵐ mapˣᵐ idᵐ μᵀ
        ∘ᵐ mapˣᵐ η⊣ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym
          (trans (cong₂ mapˣᵐ (sym []-δ⁻¹∘δ≡id) (sym (∘ᵐ-identityʳ _))) (mapˣᵐ-∘ᵐ _ _ _ _)))))) ⟩
           strᵀ
        ∘ᵐ mapˣᵐ (δ⁻¹ {τ₁ = τ} {τ₂ = τ'}) μᵀ
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ mapˣᵐ η⊣ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym T-μ∘Tstr∘str≡str∘[δ⁻¹×μ]))
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ mapˣᵐ η⊣ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
          (sym (trans (cong₂ mapˣᵐ (sym (∘ᵐ-identityʳ _)) (sym (∘ᵐ-identityˡ _))) (mapˣᵐ-∘ᵐ _ _ _ _))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (trans (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (∘ᵐ-identityˡ _)))
            (trans (∘ᵐ-congˡ (cong₂ mapˣᵐ (sym GGμ∘Gη⊣∘η⊣≡δ∘η⊣) refl)) (trans (∘ᵐ-congˡ
              (cong₂ mapˣᵐ refl (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))))
                (trans (∘ᵐ-congˡ (trans (mapˣᵐ-∘ᵐ _ _ _ _) (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _))))
                  (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) idᵐ
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (sym T-idᵐ)))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) (Tᶠ idᵐ)
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (sym (trans (cong Tᶠ T-idᵐ) T-idᵐ)))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) (Tᶠ (Tᶠ idᵐ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) (Tᶠ idᵐ)
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) (Tᶠ idᵐ)
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
         (trans
           (sym (trans (trans (⟨⟩ᵐ-∘ᵐ _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _))) (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))))
           (trans (trans
             (cong₂ ⟨_,_⟩ᵐ
               (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                 (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (⟨⟩ᵐ-fstᵐ _ _))))
                   (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (⟨⟩ᵐ-fstᵐ _ _))))
                     (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-fstᵐ _ _)
                       (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-fstᵐ _ _) (sym (∘ᵐ-identityʳ _)))))))))))))
               (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                 (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
                   (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))) (sym (trans (∘ᵐ-assoc _ _ _)
                     (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))))))))))))))
             (⟨⟩ᵐ-∘ᵐ _ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (sym []-idᵐ) refl)))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _)))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (sym T-Tassoc⁻¹∘str∘[monoidal×id]∘assoc≡str∘[str×id]))
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
            (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
              (⟨⟩ᵐ-fstᵐ _ _)
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))))
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _)))))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ⟨ ⟨ η⊣ , η⊣ ⟩ᵐ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (trans (cong₂ ⟨_,_⟩ᵐ
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))
                (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _)))))))
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (⟨⟩ᵐ-sndᵐ _ _))))) (⟨⟩ᵐ-∘ᵐ _ _ _))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ mapˣᵐ ⟨ [ τ ]ᶠ idᵐ , [ τ ]ᶠ idᵐ ⟩ᵐ idᵐ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ ([]-monoidal-⟨⟩ᵐ _ _) (∘ᵐ-identityˡ _))))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ⟨ idᵐ , idᵐ ⟩ᵐ) idᵐ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
          (cong₂ mapˣᵐ refl (sym T-idᵐ))))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ⟨ idᵐ , idᵐ ⟩ᵐ) (Tᶠ idᵐ)
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _)))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ Tᶠ (mapˣᵐ ⟨ idᵐ , idᵐ ⟩ᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ (   Tᶠ (mapˣᵐ idᵐ ⟦ N ⟧ᶜᵗ)
            ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
            ∘ᵐ Tᶠ (mapˣᵐ ⟨ idᵐ , idᵐ ⟩ᵐ idᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym
          (trans (trans (cong Tᶠ (trans (trans (sym
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-fstᵐ _ _)
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                  (trans (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))) (∘ᵐ-identityˡ _)))))))
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))
                (trans (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                    (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _)))))
                  (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
                (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-unique _ _ _ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))) (∘ᵐ-identityʳ _))))))))
            (⟨⟩ᵐ-∘ᵐ _ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))) (T-∘ᵐ _ _)) (∘ᵐ-congʳ (T-∘ᵐ _ _)))))))) ⟩
           μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ ⟨ fstᵐ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (trans (sym (T-∘ᵐ _ _)) (trans (cong Tᶠ (strᵀ-nat _ _)) (T-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
           μᵀ
        ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ ⟨ fstᵐ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (μᵀ-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
           Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)
        ∘ᵐ μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ Tᶠ ⟨ fstᵐ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ∎)) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ Tᶠ ⟨ fstᵐ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
        (trans (sym (T-∘ᵐ _ _)) (trans (cong Tᶠ
          (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (trans
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (η⊣-nat _))))))
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ
                (trans (⟨⟩ᵐ-sndᵐ _ _) (sym (⟨⟩ᵐ-sndᵐ _ _)))) (sym (∘ᵐ-assoc _ _ _)))))
            (⟨⟩ᵐ-∘ᵐ _ _ _)))) (T-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _))))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) idᵐ)
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
      (trans (∘ᵐ-congˡ (trans (sym (T-∘ᵐ _ _)) (trans (cong Tᶠ
        (trans (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (sym T-idᵐ)))
          (strᵀ-nat _ _))) (T-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _)))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
      (trans (∘ᵐ-congˡ (sym (μᵀ-nat _))) (∘ᵐ-assoc _ _ _)))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (μᵀ-nat _))) (∘ᵐ-assoc _ _ _))) ⟩
       μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ ⟦ P ⟧ᶜᵗ)
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym
      (trans
        (∘ᵐ-congˡ
          (trans
            (cong Tᶠ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))
            (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _)))))
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (τ-substᵀ-trans _ _)
      (trans (cong τ-substᵀ uip) τ-substᵀ-refl)))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ τ-substᵀ (+-assoc τ τ' τ'')
    ∘ᵐ μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ T-μ∘μ≡μ∘Tμ)
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym
      (trans
        (∘ᵐ-congˡ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))))
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (   μᵀ
           ∘ᵐ Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ)
           ∘ᵐ strᵀ
           ∘ᵐ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ)
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong Tᶠ (sym (C-rename≡∘ᵐ (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (   μᵀ
           ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P ⟧ᶜᵗ
           ∘ᵐ strᵀ
           ∘ᵐ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ)
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ ⟦ M ; (N ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P) ⟧ᶜᵗ
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ (sym (+-assoc τ τ' τ'')) _) ⟩
      ⟦ τ-subst (sym (+-assoc τ τ' τ'')) (M ;
          (N ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P)) ⟧ᶜᵗ
  ∎


{-
;-assoc-sound {Γ} {A} {B} {C} {τ} {τ'} {τ''} M N P = 
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ ,
            μᵀ
         ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
         ∘ᵐ strᵀ
         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans
      (cong₂ ⟨_,_⟩ᵐ
        (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
          (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ []-δ⁻¹∘δ≡id) (∘ᵐ-identityˡ _))))))
        (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))) (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ mapˣᵐ δ⁻¹ μᵀ
    ∘ᵐ ⟨    δ {τ₁ = τ} {τ₂ = τ'}
         ∘ᵐ η⊣ ,
            Tᶠ ⟦ N ⟧ᶜᵗ
         ∘ᵐ strᵀ
         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym T-μ∘Tstr∘str≡str∘[δ⁻¹×μ]))
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨    δ {τ₁ = τ} {τ₂ = τ'}
         ∘ᵐ η⊣ ,
            Tᶠ ⟦ N ⟧ᶜᵗ
         ∘ᵐ strᵀ
         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (sym GGμ∘Gη⊣∘η⊣≡δ∘η⊣) refl))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨    [ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))
         ∘ᵐ [ τ ]ᶠ η⊣
         ∘ᵐ η⊣ ,
            Tᶠ ⟦ N ⟧ᶜᵗ
         ∘ᵐ strᵀ
         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           strᵀ
        ∘ᵐ ⟨    [ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))
             ∘ᵐ [ τ ]ᶠ η⊣
             ∘ᵐ η⊣ ,
                Tᶠ ⟦ N ⟧ᶜᵗ
             ∘ᵐ strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (cong₂ ⟨_,_⟩ᵐ
          (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-congˡ T-idᵐ) (∘ᵐ-identityˡ _)))))) (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
           strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) (Tᶠ idᵐ)
        ∘ᵐ ⟨    [ τ ]ᶠ η⊣
             ∘ᵐ η⊣ ,
                Tᶠ ⟦ N ⟧ᶜᵗ
             ∘ᵐ strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _)) ⟩
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ ⟨    [ τ ]ᶠ η⊣
             ∘ᵐ η⊣ ,
                Tᶠ ⟦ N ⟧ᶜᵗ
             ∘ᵐ strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (cong₂ mapˣᵐ refl (sym T-idᵐ))) ⟩
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ ⟨    [ τ ]ᶠ η⊣
             ∘ᵐ η⊣ ,
                Tᶠ ⟦ N ⟧ᶜᵗ
             ∘ᵐ strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (trans (cong₂ ⟨_,_⟩ᵐ
          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
            (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _)))))))
          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-congʳ
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))))))
          (⟨⟩ᵐ-∘ᵐ _ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) (Tᶠ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _))) ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym T-Tassoc⁻¹∘str∘[monoidal×id]∘assoc≡str∘[str×id]))
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))) ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ η⊣ ⟦ N ⟧ᶜᵗ)
        ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ (   Tᶠ (mapˣᵐ η⊣ ⟦ N ⟧ᶜᵗ)
            ∘ᵐ Tᶠ ×ᵐ-assoc⁻¹)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ {!!} ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ (   Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
            ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
            ∘ᵐ Tᶠ (mapˣᵐ fstᵐ idᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ Tᶠ (mapˣᵐ fstᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (strᵀ-nat _ _))) (∘ᵐ-assoc _ _ _))))) ⟩
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ fstᵐ) (Tᶠ idᵐ)
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (trans
            (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))))
            (trans
              (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))
              (trans
                (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                (trans (cong₂ ⟨_,_⟩ᵐ
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                    (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ []-monoidal-fstᵐ)
                        (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                          (trans (⟨⟩ᵐ-fstᵐ _ _) (sym
                            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _))))))))))))
                  (trans
                    (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                      (trans
                        (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))
                        (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                          (trans (∘ᵐ-congˡ T-idᵐ) (∘ᵐ-identityˡ _))))))) (⟨⟩ᵐ-∘ᵐ _ _ _)))))))) ⟩
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ sndᵐ
        ∘ᵐ ⟨ η⊣ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _)))
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _)))))))) ⟩ 
           Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
        ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ strᵀ
        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ∎)))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ))
    ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (T-∘ᵐ _ _)) (trans (cong Tᶠ (strᵀ-nat _ _)) (T-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨ τ' ⟩ᶠ fstᵐ)) (Tᶠ idᵐ))
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (T-∘ᵐ _ _)) (trans (cong Tᶠ (strᵀ-nat _ _)) (T-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _)))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ P ⟧ᶜᵗ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (μᵀ-nat _))) (∘ᵐ-assoc _ _ _))) ⟩
       μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ ⟦ P ⟧ᶜᵗ)
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ Tᶠ (Tᶠ (mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym
      (trans
        (∘ᵐ-congˡ
          (trans
            (cong Tᶠ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))
            (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _)))))
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (τ-substᵀ-trans _ _)
      (trans (cong τ-substᵀ uip) τ-substᵀ-refl)))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ τ-substᵀ (+-assoc τ τ' τ'')
    ∘ᵐ μᵀ
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ T-μ∘μ≡μ∘Tμ)
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ μᵀ
    ∘ᵐ Tᶠ (Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ))
    ∘ᵐ Tᶠ strᵀ
    ∘ᵐ Tᶠ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym
      (trans
        (∘ᵐ-congˡ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))))
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (   μᵀ
           ∘ᵐ Tᶠ (   ⟦ P ⟧ᶜᵗ
                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ
                  ∘ᵐ mapˣᵐ (⟨ τ' ⟩ᶠ fstᵐ) idᵐ)
           ∘ᵐ strᵀ
           ∘ᵐ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ)
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong Tᶠ (sym (C-rename≡∘ᵐ (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ μᵀ
    ∘ᵐ Tᶠ (   μᵀ
           ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P ⟧ᶜᵗ
           ∘ᵐ strᵀ
           ∘ᵐ ⟨ η⊣ , ⟦ N ⟧ᶜᵗ ⟩ᵐ)
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ≡⟨⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ ⟦ M ; (N ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P) ⟧ᶜᵗ
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ (sym (+-assoc τ τ' τ'')) _) ⟩
      ⟦ τ-subst (sym (+-assoc τ τ' τ'')) (M ;
          (N ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) P)) ⟧ᶜᵗ
  ∎
-}
