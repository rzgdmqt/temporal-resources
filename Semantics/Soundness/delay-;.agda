-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.delay-; (Mod : Model) where

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

delay-;-sound : ∀ {Γ A B τ τ' τ''}
              → (M : Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ')
              → (N : Γ ⟨ τ + τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
              → ⟦ delay τ M ; N ⟧ᶜᵗ
              ≡ ⟦ τ-subst (sym (+-assoc τ τ' τ''))
                    (delay τ (M ; C-rename (cong-∷-ren ⟨⟩-μ-ren) N)) ⟧ᶜᵗ

delay-;-sound {Γ} {A} {B} {τ} {τ'} {τ''} M N = 
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ , delayᵀ τ ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ {!!} ⟩
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
      ≡⟨ {!!} ⟩
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
  ≡⟨ sym (τ-subst≡∘ᵐ _ _) ⟩
    ⟦ τ-subst (sym (+-assoc τ τ' τ''))
        (delay τ (M ; C-rename (cong-∷-ren ⟨⟩-μ-ren) N)) ⟧ᶜᵗ
  ∎
