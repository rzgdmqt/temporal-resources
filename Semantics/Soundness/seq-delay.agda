-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.seq-delay (Mod : Model) where

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

seq-delay-sound : ∀ {Γ A B τ τ' τ''}
              → (M : Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ')
              → (N : Γ ⟨ τ + τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
              → ⟦ delay τ M ; N ⟧ᶜᵗ
              ≡ ⟦ τ-subst (sym (+-assoc τ τ' τ''))
                    (delay τ (M ; C-rename (cong-∷-ren ⟨⟩-μ-ren) N)) ⟧ᶜᵗ

seq-delay-sound {Γ} {A} {B} {τ} {τ'} {τ''} M N = 
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , delayᵀ τ ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans
      (cong₂ ⟨_,_⟩ᵐ
        (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _))))
        (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))) (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ)
    ∘ᵐ ⟨ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ strᵀ-delayᵀ-algebraicity)
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ strᵀ
    ∘ᵐ []-monoidal
    ∘ᵐ mapˣᵐ δ idᵐ
    ∘ᵐ ⟨ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (delayᵀ-nat τ _))) (∘ᵐ-assoc _ _ _))) ⟩
       μᵀ
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ [ τ ]ᶠ strᵀ
    ∘ᵐ []-monoidal
    ∘ᵐ mapˣᵐ δ idᵐ
    ∘ᵐ ⟨ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (delayᵀ-algebraicity τ))
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ μᵀ
    ∘ᵐ [ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ [ τ ]ᶠ strᵀ
    ∘ᵐ []-monoidal
    ∘ᵐ mapˣᵐ δ idᵐ
    ∘ᵐ ⟨ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           [ τ ]ᶠ strᵀ
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ ⟨ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
          begin
            ⟨ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ cong ⟨_, [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ (sym
              (begin
                    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
                 ∘ᵐ δ⁻¹
                 ∘ᵐ [ τ ]ᶠ η⊣
                 ∘ᵐ η⊣
               ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ ([]-δ⁻¹-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
                    δ⁻¹
                 ∘ᵐ [ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))
                 ∘ᵐ [ τ ]ᶠ η⊣
                 ∘ᵐ η⊣
               ≡⟨ ∘ᵐ-congʳ GGμ∘Gη⊣∘η⊣≡δ∘η⊣ ⟩
                    δ⁻¹
                 ∘ᵐ δ
                 ∘ᵐ η⊣
               ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ []-δ⁻¹∘δ≡id) ⟩
                    idᵐ
                 ∘ᵐ η⊣
               ≡⟨ ∘ᵐ-identityˡ _ ⟩
                 η⊣
               ∎)) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ δ⁻¹
              ∘ᵐ [ τ ]ᶠ η⊣
              ∘ᵐ η⊣
              ,
                 [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
              ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)))))
              (sym (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ δ⁻¹
              ∘ᵐ [ τ ]ᶠ η⊣
              ∘ᵐ idᵐ
              ∘ᵐ η⊣
              ,
                 idᵐ
              ∘ᵐ idᵐ
              ∘ᵐ idᵐ
              ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
              ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))))))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))))))) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ δ⁻¹
              ∘ᵐ [ τ ]ᶠ η⊣
              ∘ᵐ fstᵐ
              ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
              ∘ᵐ η⊣
              ,
                 idᵐ
              ∘ᵐ idᵐ
              ∘ᵐ idᵐ
              ∘ᵐ sndᵐ
              ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
              ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ δ⁻¹
              ∘ᵐ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ)
              ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
              ∘ᵐ η⊣
              ,
                 idᵐ
              ∘ᵐ idᵐ
              ∘ᵐ (idᵐ ∘ᵐ sndᵐ)
              ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _))))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)))) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ δ⁻¹
              ∘ᵐ fstᵐ
              ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                   (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
              ,
                 idᵐ
              ∘ᵐ idᵐ
              ∘ᵐ sndᵐ
              ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                   (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ (δ⁻¹ ∘ᵐ fstᵐ)
              ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                   (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
              ,
                 idᵐ
              ∘ᵐ (idᵐ ∘ᵐ sndᵐ)
              ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                   (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩
            ⟨    [ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)
              ∘ᵐ fstᵐ
              ∘ᵐ ⟨   (δ⁻¹ ∘ᵐ fstᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
                  ,
                     (idᵐ ∘ᵐ sndᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
              ,
                 idᵐ
              ∘ᵐ sndᵐ
              ∘ᵐ ⟨   (δ⁻¹ ∘ᵐ fstᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
                  ,
                     (idᵐ ∘ᵐ sndᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
          ≡⟨ cong₂ ⟨_,_⟩ᵐ (sym (∘ᵐ-assoc _ _ _)) (sym (∘ᵐ-assoc _ _ _)) ⟩
            ⟨    ([ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) ∘ᵐ fstᵐ)
              ∘ᵐ ⟨   (δ⁻¹ ∘ᵐ fstᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
                  ,
                     (idᵐ ∘ᵐ sndᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
              ,
                 (idᵐ ∘ᵐ sndᵐ)
              ∘ᵐ ⟨   (δ⁻¹ ∘ᵐ fstᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ
                  ,
                     (idᵐ ∘ᵐ sndᵐ)
                  ∘ᵐ ⟨ ([ τ ]ᶠ η⊣ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ,
                       (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
          ≡⟨ sym (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))))
              (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))) (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
               mapˣᵐ ([ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ
            ∘ᵐ mapˣᵐ δ⁻¹ idᵐ
            ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) idᵐ ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
            ∘ᵐ η⊣
          ∎))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ mapˣᵐ ([ τ + τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ
        ∘ᵐ mapˣᵐ δ⁻¹ idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) idᵐ
        ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (trans (cong₂ mapˣᵐ ([]-δ⁻¹-nat _) refl) (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ mapˣᵐ δ⁻¹ idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) idᵐ
        ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (trans (cong₂ mapˣᵐ []-δ∘δ⁻¹≡id (∘ᵐ-identityˡ _)) mapˣᵐ-identity))) (∘ᵐ-identityˡ _)))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) idᵐ
        ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (sym (trans ([]-monoidal-nat _ _) (∘ᵐ-congʳ (cong₂ mapˣᵐ refl []-idᵐ))))) (∘ᵐ-assoc _ _ _))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ η⊣) idᵐ
        ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (trans (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (sym []-idᵐ))) (sym ([]-monoidal-nat _ _)))) (∘ᵐ-assoc _ _ _)))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ ⟨ idᵐ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (
          trans (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (sym []-idᵐ) refl)) ([]-monoidal-⟨⟩ᵐ _ _)))))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ [ τ ]ᶠ ⟨ idᵐ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
          (trans (sym ([]-∘ᵐ _ _)) (cong [ τ ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityʳ _)))
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _)))))))))) ⟩
           [ τ ]ᶠ strᵀ
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (trans (sym ([]-∘ᵐ _ _)) (trans (cong [ τ ]ᶠ (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (sym T-idᵐ))))
            (trans (cong [ τ ]ᶠ (strᵀ-nat _ _)) ([]-∘ᵐ _ _))))) (∘ᵐ-assoc _ _ _)) ⟩
           [ τ ]ᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
        ∘ᵐ [ τ ]ᶠ strᵀ
        ∘ᵐ [ τ ]ᶠ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
        ∘ᵐ η⊣
      ∎)))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ μᵀ
    ∘ᵐ [ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ [ τ ]ᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ [ τ ]ᶠ strᵀ
    ∘ᵐ [ τ ]ᶠ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym
      (trans (∘ᵐ-congˡ (cong [ τ ]ᶠ (T-∘ᵐ _ _)))
        (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ μᵀ
    ∘ᵐ [ τ ]ᶠ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                   ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
    ∘ᵐ [ τ ]ᶠ strᵀ
    ∘ᵐ [ τ ]ᶠ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ (   [ τ ]ᶠ μᵀ
        ∘ᵐ [ τ ]ᶠ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                       ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
        ∘ᵐ [ τ ]ᶠ strᵀ
        ∘ᵐ [ τ ]ᶠ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym
      (trans ([]-∘ᵐ _ _) (∘ᵐ-congʳ (trans ([]-∘ᵐ _ _) (∘ᵐ-congʳ ([]-∘ᵐ _ _)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   μᵀ
               ∘ᵐ Tᶠ (   ⟦ N ⟧ᶜᵗ
                      ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)
               ∘ᵐ strᵀ
               ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   μᵀ
               ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ ⟦ cong-∷-ren {A = A} (⟨⟩-μ-ren {Γ}) ⟧ʳ)
               ∘ᵐ strᵀ
               ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong Tᶠ (sym (C-rename≡∘ᵐ (cong-∷-ren ⟨⟩-μ-ren) N)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   μᵀ
               ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren ⟨⟩-μ-ren) N ⟧ᶜᵗ
               ∘ᵐ strᵀ
               ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ ⟦ delay τ (M ; C-rename (cong-∷-ren ⟨⟩-μ-ren) N) ⟧ᶜᵗ
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ _ _) ⟩
    ⟦ τ-subst (sym (+-assoc τ τ' τ''))
        (delay τ (M ; C-rename (cong-∷-ren ⟨⟩-μ-ren) N)) ⟧ᶜᵗ
  ∎
