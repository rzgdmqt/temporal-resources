-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.delay-handle (Mod : Model) where

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

delay-handle-sound : ∀ {Γ A B τ τ' τ''}
                   → (M : Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ')
                   → (H : (op : Op) (τ''' : Time)
                        → Γ ∷ type-of-gtype (param op) ∷
                            [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ''')
                              ⊢C⦂ B ‼ (op-time op + τ'''))
                   → (N : Γ ⟨ τ + τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
                   → ⟦ handle delay τ M `with H `in N ⟧ᶜᵗ
                   ≡ ⟦ τ-subst (sym (+-assoc τ τ' τ''))
                         (delay τ
                          (handle M `with
                           (λ op τ''' →
                              C-rename (cong-∷-ren (cong-∷-ren (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren)))
                              (H op τ'''))
                           `in
                           (C-rename (cong-∷-ren ⟨⟩-μ-ren) N))) ⟧ᶜᵗ

delay-handle-sound {Γ} {A} {B} {τ} {τ'} {τ''} M H N =
  begin
       uncurryᵐ (   T-alg-of-handlerᵀ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
    ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ mapˣᵐ idᵐ strᵀ 
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , delayᵀ τ ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (trans (trans
      (cong₂ ⟨_,_⟩ᵐ
        (sym (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))
        (trans (trans (trans
          (cong₂ ⟨_,_⟩ᵐ
            (sym (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (∘ᵐ-identityʳ _))))
            (sym (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))
          (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (∘ᵐ-congʳ (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))
      (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (∘ᵐ-congʳ (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))) ⟩
       uncurryᵐ (   T-alg-of-handlerᵀ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
    ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ mapˣᵐ idᵐ strᵀ 
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (delayᵀ τ))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (cong (mapˣᵐ (idᵐ ∘ᵐ idᵐ)) strᵀ-delayᵀ-algebraicity)))
        (trans (∘ᵐ-congˡ (cong₂ mapˣᵐ (sym (∘ᵐ-identityˡ _)) refl))
          (trans (∘ᵐ-congˡ (trans (mapˣᵐ-∘ᵐ _ _ _ _) (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _))))
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
              (trans (∘ᵐ-congˡ (cong₂ mapˣᵐ (sym (∘ᵐ-identityˡ _)) refl))
                (trans (∘ᵐ-congˡ (mapˣᵐ-∘ᵐ _ _ _ _)) (∘ᵐ-assoc _ _ _)))))))))))) ⟩
       uncurryᵐ (   T-alg-of-handlerᵀ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
    ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ) 
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
    ∘ᵐ mapˣᵐ idᵐ []-monoidal
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans (cong (mapˣᵐ (idᵐ ∘ᵐ idᵐ))
        (sym (delayᵀ-nat τ _))) (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
       uncurryᵐ (   T-alg-of-handlerᵀ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
    ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ)
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
    ∘ᵐ mapˣᵐ idᵐ []-monoidal
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (∘ᵐ-congˡ (uncurryᵐ-nat _ _)) (∘ᵐ-assoc _ _ _) ⟩
       uncurryᵐ T-alg-of-handlerᵀ
    ∘ᵐ mapˣᵐ (   ⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
              ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ
    ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ)
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
    ∘ᵐ mapˣᵐ idᵐ []-monoidal
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans
        (cong₂ mapˣᵐ
          (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
          (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))
      (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
       uncurryᵐ T-alg-of-handlerᵀ
    ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ)
    ∘ᵐ mapˣᵐ (   ⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
              ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
    ∘ᵐ mapˣᵐ idᵐ []-monoidal
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ T-alg-of-handlerᵀ-delayᵀ)
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (uncurryᵐ T-alg-of-handlerᵀ)
    ∘ᵐ [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
    ∘ᵐ []-monoidal
    ∘ᵐ mapˣᵐ η⊣ idᵐ
    ∘ᵐ mapˣᵐ (   ⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
              ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
    ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
    ∘ᵐ mapˣᵐ idᵐ []-monoidal
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
    ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ (   ⟨ (λ op → ⟨ (λ τ''' →
                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ
        ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
        ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
            (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans
              (cong₂ mapˣᵐ (sym (η⊣-nat _)) (∘ᵐ-congˡ (sym []-idᵐ)))
            (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _)))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                 ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                             ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                          ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))) ([ τ ]ᶠ idᵐ)
        ∘ᵐ mapˣᵐ η⊣ idᵐ
        ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
        ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
            begin
                 mapˣᵐ η⊣ idᵐ
              ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
              ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
            ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans
                  (cong₂ mapˣᵐ
                    (trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))))
                    (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))
                (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _)) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ η⊣ idᵐ
              ∘ᵐ mapˣᵐ idᵐ ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
              ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                (trans (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                  (trans
                    (cong₂ mapˣᵐ
                      (trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))))
                      (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))
                  (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ η⊣ idᵐ
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
              ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans
                  (cong₂ mapˣᵐ
                    (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
                    (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))
                (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _)))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ mapˣᵐ η⊣ idᵐ
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ δ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
              ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
                  (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                    (cong₂ mapˣᵐ
                      (trans (∘ᵐ-congˡ []-idᵐ) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))))
                      (sym (trans (∘ᵐ-identityˡ _) (sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
                        (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                          (cong₂ mapˣᵐ
                            (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _)))
                              (trans (∘ᵐ-congˡ (cong [ τ ]ᶠ (trans (sym ([]-∘ᵐ _ _)) (cong [ τ' ]ᶠ
                                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                                  (∘ᵐ-congˡ ⟨⟩-μ∘μ⁻¹≡id))) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                    (trans
                                      (⟨⟩-≤-trans (≤-reflexive (+-comm τ τ')) (≤-reflexive (sym (+-comm τ τ'))))
                                      (trans (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟨⟩-≤-refl)))))))))
                                        (trans (∘ᵐ-congˡ (trans (cong [ τ ]ᶠ []-idᵐ) []-idᵐ)) (∘ᵐ-identityˡ _)))))
                            (trans (∘ᵐ-congˡ (trans (cong [ τ ]ᶠ T-idᵐ) []-idᵐ))
                              (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))))))))))))))))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ (   mapˣᵐ ([ τ ]ᶠ idᵐ) (mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ {τ₁ = τ'} {τ₂ = τ}))) ([ τ ]ᶠ (Tᶠ idᵐ)))
                  ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))) idᵐ)
                  ∘ᵐ mapˣᵐ η⊣ (mapˣᵐ δ idᵐ))
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
              ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) (mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ {τ₁ = τ'} {τ₂ = τ}))) ([ τ ]ᶠ (Tᶠ idᵐ)))
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))) idᵐ)
              ∘ᵐ mapˣᵐ η⊣ (mapˣᵐ δ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
              ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
              ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
                begin
                     mapˣᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))) idᵐ)
                  ∘ᵐ mapˣᵐ η⊣ (mapˣᵐ δ idᵐ)
                  ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ)
                  ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ))
                  ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ
                ≡⟨ trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))
                    (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
                      (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (trans
                        (cong₂ ⟨_,_⟩ᵐ
                          (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-congʳ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))
                            (trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))))))
                          (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))
                            (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
                              (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
                                (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (trans
                                  (cong₂ ⟨_,_⟩ᵐ
                                    (begin
                                         [ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))
                                      ∘ᵐ δ
                                      ∘ᵐ η⊣
                                      ∘ᵐ idᵐ
                                      ∘ᵐ idᵐ
                                    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) ⟩
                                         [ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))
                                      ∘ᵐ δ
                                      ∘ᵐ η⊣
                                      ∘ᵐ idᵐ
                                    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) ⟩
                                         [ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))
                                      ∘ᵐ δ
                                      ∘ᵐ η⊣
                                    ≡⟨ ∘ᵐ-congʳ (sym GGμ∘Gη⊣∘η⊣≡δ∘η⊣) ⟩
                                         [ τ ]ᶠ ([ τ' ]ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-comm τ τ')))))
                                      ∘ᵐ [ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))
                                      ∘ᵐ [ τ ]ᶠ η⊣
                                      ∘ᵐ η⊣
                                    ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
                                        (trans (sym ([]-∘ᵐ _ _)) (trans (cong [ τ ]ᶠ
                                          (trans (sym ([]-∘ᵐ _ _)) (cong [ τ' ]ᶠ
                                            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                                              (∘ᵐ-congˡ (trans (⟨⟩-≤-trans (≤-reflexive (sym (+-comm τ τ'))) (≤-reflexive (+-comm τ τ')))
                                                (trans (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟨⟩-≤-refl))))) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                                  ⟨⟩-μ⁻¹∘μ≡id)))))) (trans (cong [ τ ]ᶠ []-idᵐ) []-idᵐ)))) ⟩
                                         idᵐ
                                      ∘ᵐ [ τ ]ᶠ η⊣
                                      ∘ᵐ η⊣
                                    ≡⟨ ∘ᵐ-identityˡ _ ⟩
                                         [ τ ]ᶠ η⊣
                                      ∘ᵐ η⊣
                                    ∎)
                                    (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))
                                  (⟨⟩ᵐ-∘ᵐ _ _ _)))))))
                      (⟨⟩ᵐ-∘ᵐ _ _ _))))) ⟩
                     ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
                  ∘ᵐ η⊣
                ∎)))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) (mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ))) ([ τ ]ᶠ (Tᶠ idᵐ)))
              ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
              ∘ᵐ η⊣
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans
                  (cong₂ mapˣᵐ
                    (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))
                    (sym ([]-monoidal-nat _ _)))
                (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _)))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (mapˣᵐ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) (Tᶠ idᵐ)))
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
              ∘ᵐ η⊣
            ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans (cong₂ mapˣᵐ refl
                  (trans (sym ([]-∘ᵐ _ _)) (trans (cong [ τ ]ᶠ (strᵀ-nat _ _)) ([]-∘ᵐ _ _))))
                (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
                 mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
              ∘ᵐ mapˣᵐ idᵐ []-monoidal
              ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
              ∘ᵐ η⊣
            ∎))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                 ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                             ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                          ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))) ([ τ ]ᶠ idᵐ)
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
            (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
            (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _)))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
            (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _))))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) ([ τ ]ᶠ strᵀ)
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
            (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _)))))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ idᵐ []-monoidal
        ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , ⟨ [ τ ]ᶠ η⊣ , [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
            (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (∘ᵐ-identityˡ _)
                ([]-monoidal-⟨⟩ᵐ _ _)))))))))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
        ∘ᵐ []-monoidal
        ∘ᵐ ⟨ [ τ ]ᶠ idᵐ , [ τ ]ᶠ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ ([]-monoidal-⟨⟩ᵐ _ _))))))) ⟩ 
           [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                  ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                  ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
        ∘ᵐ [ τ ]ᶠ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
            (begin
                 [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
              ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                                    ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                                 ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
            ≡⟨ sym ([]-∘ᵐ _ _) ⟩
              [ τ ]ᶠ (   mapˣᵐ ε-⟨⟩ idᵐ
                      ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                                    ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                                 ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)) idᵐ)
            ≡⟨ cong [ τ ]ᶠ (sym (mapˣᵐ-∘ᵐ _ _ _ _)) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       (   ε-⟨⟩
                        ∘ᵐ ⟨ τ ⟩ᶠ (   ⟨ (λ op → ⟨ (λ τ''' →
                                                  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                   ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                              ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                               ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                            ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                   ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                       (idᵐ ∘ᵐ idᵐ))
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)))
                (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-η⁻¹-nat _))) (∘ᵐ-assoc _ _ _))))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       ((   ⟨ (λ op → ⟨ (λ τ''' →
                                                  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                   ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                              ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                               ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                                            ∘ᵐ projᵐ op) ⟩ᵢᵐ
                                   ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                        ∘ᵐ ε-⟨⟩)
                       (idᵐ ∘ᵐ idᵐ))
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-assoc _ _ _) (∘ᵐ-identityˡ _)) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       (   mapⁱˣᵐ (λ op →
                             mapⁱˣᵐ (λ τ''' →
                                  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                   ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                              ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ
                        ∘ᵐ ε-⟨⟩)
                       idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _)) (trans
                (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _)) (sym
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ op)) (sym (trans
                    (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ''' → trans (∘ᵐ-identityˡ _)
                      (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ τ''')) (∘ᵐ-identityʳ _)))))))
                        (⟨⟩ᵢᵐ-∘ᵐ _ _))))) )))) (⟨⟩ᵢᵐ-∘ᵐ _ _)))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       (   mapⁱˣᵐ (λ op →
                             mapⁱˣᵐ (λ τ''' →
                                  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                   ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                              ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                        ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' → ε-⟨⟩))
                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                       idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (mapⁱˣᵐ-∘ᵐ _ _)))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       (      mapⁱˣᵐ (λ op →
                                mapⁱˣᵐ (λ τ''' →
                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                 ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))
                           ∘ᵐ mapⁱˣᵐ (λ τ''' → ε-⟨⟩))
                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                       idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong mapⁱˣᵐ (fun-ext (λ op → sym (mapⁱˣᵐ-∘ᵐ _ _))))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       (   mapⁱˣᵐ (λ op →
                             mapⁱˣᵐ (λ τ''' →
                                  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                   ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                              ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                               ∘ᵐ ε-⟨⟩))
                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                       idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext λ τ''' →
                ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ
                       (   mapⁱˣᵐ (λ op →
                             mapⁱˣᵐ (λ τ''' →
                                  map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                               ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ ε-⟨⟩))
                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                       idᵐ)
            ≡⟨⟩
              [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                         ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ ε-⟨⟩)
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext λ τ''' →
                ∘ᵐ-congˡ (∘ᵐ-congʳ (sym (curryᵐ-nat _ _))))))))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                             ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                                         ∘ᵐ mapˣᵐ ε-⟨⟩ idᵐ))
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext λ τ''' →
                ∘ᵐ-congˡ (∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-assoc _ _ _))))))))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                         ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ mapˣᵐ ε-⟨⟩ idᵐ))
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
            ≡⟨ cong [ τ ]ᶠ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext λ τ''' →
                ∘ᵐ-congˡ (∘ᵐ-congʳ (cong curryᵐ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                  (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (trans
                    (cong₂ ⟨_,_⟩ᵐ
                      (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (trans
                        (cong₂ ⟨_,_⟩ᵐ
                          (sym (⟨⟩ᵐ-fstᵐ _ _))
                          (trans (∘ᵐ-identityˡ _) (sym
                            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)))))))
                        (⟨⟩ᵐ-∘ᵐ _ _ _)))
                      (trans (∘ᵐ-identityˡ _) (sym
                        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)))))))
                    (⟨⟩ᵐ-∘ᵐ _ _ _)))))))))))))) refl) ⟩
              [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                             (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                              ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                             ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ)
                                         ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                          ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
            ∎)) ⟩
           [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                          ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ)
                                      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
        ∘ᵐ [ τ ]ᶠ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ (cong [ τ ]ᶠ (cong₂ mapˣᵐ (sym (∘ᵐ-identityˡ _)) (T-∘ᵐ _ _))))
            (trans (∘ᵐ-congˡ (cong [ τ ]ᶠ (mapˣᵐ-∘ᵐ _ _ _ _)))
              (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))) ⟩
           [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                          ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ)
                                      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                  ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
        ∘ᵐ [ τ ]ᶠ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∘ᵐ η⊣
      ∎))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (uncurryᵐ T-alg-of-handlerᵀ)
    ∘ᵐ [ τ ]ᶠ (mapˣᵐ (⟨ (λ op → ⟨ (λ τ''' →
                                 (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                  ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ)
                                             ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                              ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                           ∘ᵐ projᵐ op) ⟩ᵢᵐ
                        ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ) idᵐ)
    ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                              ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
    ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
    ∘ᵐ [ τ ]ᶠ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ (cong [ τ ]ᶠ (uncurryᵐ-nat _ _)))
      (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   uncurryᵐ (T-alg-of-handlerᵀ
                            ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                     ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ)
                                                ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                 ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                              ∘ᵐ projᵐ op) ⟩ᵢᵐ
                           ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
    ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                              ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ)))
    ∘ᵐ [ τ ]ᶠ (mapˣᵐ idᵐ strᵀ)
    ∘ᵐ [ τ ]ᶠ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ
      (trans ([]-∘ᵐ _ _) (∘ᵐ-congʳ (trans ([]-∘ᵐ _ _) (∘ᵐ-congʳ ([]-∘ᵐ _ _))))))
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   uncurryᵐ (T-alg-of-handlerᵀ
                            ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                     ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ)
                                                ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                 ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                              ∘ᵐ projᵐ op) ⟩ᵢᵐ
                           ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                 ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) idᵐ))
               ∘ᵐ mapˣᵐ idᵐ strᵀ 
               ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ''' →
        ∘ᵐ-congˡ (∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congˡ (sym
          (C-rename≡∘ᵐ (cong-∷-ren (cong-∷-ren (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren))) (H op τ'''))))))))))))))))))) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   uncurryᵐ (T-alg-of-handlerᵀ
                            ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                     ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren))) (H op τ''') ⟧ᶜᵗ
                                                ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                 ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                              ∘ᵐ projᵐ op) ⟩ᵢᵐ
                           ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                       Tᶠ (   ⟦ N ⟧ᶜᵗ
                           ∘ᵐ ⟨ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                    ∘ᵐ sndᵐ ⟩ᵐ
               ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
               ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ idᵐ ∘ᵐ fstᵐ ,_⟩ᵐ (∘ᵐ-congˡ (cong Tᶠ
      (sym (C-rename≡∘ᵐ (cong-∷-ren ⟨⟩-μ-ren) N)))))))) )) ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   uncurryᵐ (T-alg-of-handlerᵀ
                            ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                     ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren))) (H op τ''') ⟧ᶜᵗ
                                                ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                 ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                              ∘ᵐ projᵐ op) ⟩ᵢᵐ
                           ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ C-rename (cong-∷-ren ⟨⟩-μ-ren) N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
               ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
               ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ (sym (+-assoc τ τ' τ'')) _) ⟩
      ⟦ τ-subst (sym (+-assoc τ τ' τ''))
          (delay τ
           (handle M `with
            (λ op τ''' →
               C-rename (cong-∷-ren (cong-∷-ren (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren)))
               (H op τ'''))
            `in
            (C-rename (cong-∷-ren ⟨⟩-μ-ren) N))) ⟧ᶜᵗ
  ∎
