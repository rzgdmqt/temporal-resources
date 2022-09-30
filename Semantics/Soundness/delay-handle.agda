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
  ≡⟨ {!!} ⟩
       τ-substᵀ (sym (+-assoc τ τ' τ''))
    ∘ᵐ delayᵀ τ
    ∘ᵐ [ τ ]ᶠ (   uncurryᵐ (T-alg-of-handlerᵀ
                            ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                     ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ (mapˣᵐ (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) idᵐ) idᵐ)
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
