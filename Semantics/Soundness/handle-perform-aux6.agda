-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux6 (Mod : Model) where

open import Data.Product

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

open import Semantics.Soundness.handle-perform-aux7 Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

handle-perform-sound-aux6 : ∀ {Γ A B τ τ'} → (op : Op)
                          → (V : Γ ⊢V⦂ type-of-gtype (param op))
                          → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                          → (H : (op : Op) (τ'' : Time)
                               → Γ ∷ type-of-gtype (param op) ∷
                                  [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                    ⊢C⦂ B ‼ (op-time op + τ''))
                          → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                          →   ×ᵐ-assoc⁻¹
                           ∘ᵐ ⟨ fstᵐ ,
                                ⟨    fstᵐ
                                  ∘ᵐ sndᵐ ,
                                     [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                                           ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                                            (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                                             ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                                        ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                                        ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                                           ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                                              ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                              ∘ᵐ ×ᵐ-assoc
                                                              ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                                              ∘ᵐ mapˣᵐ
                                                                   (mapˣᵐ
                                                                      idᵐ
                                                                      (curryᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                                                      ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                                                               ∘ᵐ strᵀ
                                                                               ∘ᵐ ⟨   η⊣
                                                                                   ∘ᵐ fstᵐ ,
                                                                                      ⟦ M ⟧ᶜᵗ
                                                                                   ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                                                                   ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ)))
                                                                   idᵐ))
                                  ∘ᵐ []-monoidal
                                  ∘ᵐ ⟨    η⊣
                                       ∘ᵐ fstᵐ ,
                                          sndᵐ
                                       ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                                           idᵐ
                                           (   []-monoidal
                                            ∘ᵐ mapˣᵐ η⊣ idᵐ))
                           ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
                           ≡
                              mapˣᵐ (⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ) idᵐ
                           ∘ᵐ mapˣᵐ
                                idᵐ
                                ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapⁱˣᵐ (λ op →
                                                                           mapⁱˣᵐ (λ τ''' →
                                                                              (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                               ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                              ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                                          ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                                         ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                                           ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                                         ∘ᵐ mapˣᵐ idᵐ strᵀ
                                                         ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)))
                           ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ

handle-perform-sound-aux6 {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                       ∘ᵐ mapˣᵐ
                                            (mapˣᵐ
                                               idᵐ
                                               (curryᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                               ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ ⟨   η⊣
                                                            ∘ᵐ fstᵐ ,
                                                               ⟦ M ⟧ᶜᵗ
                                                            ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                                            ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ)))
                                            idᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (∘ᵐ-identityˡ _)
            (∘ᵐ-identityʳ _)))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ
                                            (mapˣᵐ
                                               idᵐ
                                               (curryᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                               ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ ⟨   η⊣
                                                            ∘ᵐ fstᵐ ,
                                                               ⟦ M ⟧ᶜᵗ
                                                            ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                                            ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ)))
                                            (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (trans (∘ᵐ-identityˡ _) (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-congˡ (∘ᵐ-identityˡ _))))))))
            (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (sym (∘ᵐ-assoc _ _ _))
                  (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-assoc _ _ _)))))
                (trans (⟨⟩ᵐ-sndᵐ _ _) (sym (∘ᵐ-identityˡ _))))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                                                      (curryᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                               ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                                         ∘ᵐ strᵀ
                                                         ∘ᵐ ⟨   η⊣
                                                             ∘ᵐ fstᵐ ,
                                                                ⟦ M ⟧ᶜᵗ
                                                             ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                                             ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ))
                                                      idᵐ)
                                       ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ ,
                                            ⟨    sndᵐ
                                              ∘ᵐ fstᵐ ,
                                                 (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                              ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
        (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (sym (∘ᵐ-identityˡ _))
              (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (uncurryᵐ-nat _ _))
                (cong uncurryᵐ (∘ᵐ-identityˡ _)))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ (curryᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                                              ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                                                       ∘ᵐ strᵀ
                                                                       ∘ᵐ ⟨   η⊣
                                                                           ∘ᵐ fstᵐ ,
                                                                              ⟦ M ⟧ᶜᵗ
                                                                           ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                                                           ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ)))
                                       ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ ,
                                            ⟨    sndᵐ
                                              ∘ᵐ fstᵐ ,
                                                 (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                              ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong₂ mapˣᵐ
          refl
          (curryᵐ-uncurryᵐ-iso _)))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                            ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                                     ∘ᵐ strᵀ
                                                     ∘ᵐ ⟨   η⊣
                                                         ∘ᵐ fstᵐ ,
                                                            ⟦ M ⟧ᶜᵗ
                                                         ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                                         ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ)
                                       ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ ,
                                            ⟨    sndᵐ
                                              ∘ᵐ fstᵐ ,
                                                 (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                              ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
        (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
          (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))
              (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                            ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                       ∘ᵐ mapˣᵐ idᵐ strᵀ
                                       ∘ᵐ mapˣᵐ
                                            idᵐ
                                            ⟨   η⊣
                                             ∘ᵐ fstᵐ ,
                                                ⟦ M ⟧ᶜᵗ
                                             ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))
                                             ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ
                                       ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ ,
                                            ⟨    sndᵐ
                                              ∘ᵐ fstᵐ ,
                                                 (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                              ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
        (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (∘ᵐ-identityˡ _)
            (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
                (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
                  (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
                    (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                      (cong₂ ⟨_,_⟩ᵐ
                        (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-assoc _ _ _)))
                        (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (sym (∘ᵐ-assoc _ _ _)))))))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                            ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                       ∘ᵐ mapˣᵐ idᵐ strᵀ
                                       ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ ,
                                            ⟨    η⊣
                                              ∘ᵐ sndᵐ
                                              ∘ᵐ fstᵐ ,
                                                 ⟦ M ⟧ᶜᵗ
                                              ∘ᵐ mapˣᵐ
                                                   (sndᵐ ∘ᵐ sndᵐ)
                                                   (⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))) ⟩ᵐ ⟩ᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
        (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (sym (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
            (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                  (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))))
                (trans (∘ᵐ-identityˡ _) (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (
                  cong₂ ⟨_,_⟩ᵐ
                    refl
                    (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (⟦⟧ᵛ-⟦⟧ᵍ-iso (arity op))))))))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                       ∘ᵐ mapˣᵐ fstᵐ idᵐ
                                       ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                            ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                       ∘ᵐ mapˣᵐ idᵐ strᵀ
                                       ∘ᵐ ⟨ fstᵐ ,
                                            ⟨    η⊣
                                              ∘ᵐ sndᵐ
                                              ∘ᵐ fstᵐ ,
                                                 ⟦ M ⟧ᶜᵗ
                                              ∘ᵐ mapˣᵐ
                                                   (sndᵐ ∘ᵐ sndᵐ)
                                                   idᵐ ⟩ᵐ ⟩ᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨  handle-perform-sound-aux7 {Γ} {A} {B} {τ} {τ'} op V M H N  ⟩
       mapˣᵐ (⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ) idᵐ
    ∘ᵐ mapˣᵐ
         idᵐ
         ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)))
    ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
  ∎
