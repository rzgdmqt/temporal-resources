-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux7 (Mod : Model) where

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

open import Semantics.Soundness.handle-perform-aux8 Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod


handle-perform-sound-aux7 : ∀ {Γ A B τ τ'} → (op : Op)
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

handle-perform-sound-aux7 {Γ} {A} {B} {τ} {τ'} op V M H N =
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
      (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ
          refl
          (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              refl
              (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (cong₂ ⟨_,_⟩ᵐ
                    refl
                    (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))))))))))))))))))) ⟩
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
                     ∘ᵐ mapˣᵐ η⊣ η⊣))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _))
        (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
              (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-congˡ (∘ᵐ-identityˡ _))))))
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
              (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                (cong₂ ⟨_,_⟩ᵐ
                  (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)))))
                  (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                    (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-assoc _ _ _)))))))))))))))))))) ⟩
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
           ∘ᵐ mapˣᵐ
                η⊣
                (   []-monoidal
                 ∘ᵐ mapˣᵐ η⊣ η⊣)
           ∘ᵐ ⟨    fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op →
                                                        mapⁱˣᵐ (λ τ''' →
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
           ∘ᵐ mapˣᵐ
                η⊣
                (   []-monoidal
                 ∘ᵐ mapˣᵐ η⊣ η⊣)
           ∘ᵐ ⟨    fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (⟨⟩ᵐ-fstᵐ _ _)
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))))
        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _)))))) ⟩
       ⟨ ⟨ fstᵐ ,
              fstᵐ
           ∘ᵐ sndᵐ ⟩ᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                    ∘ᵐ mapⁱˣᵐ (λ op →
                                                        mapⁱˣᵐ (λ τ''' →
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
           ∘ᵐ mapˣᵐ
                η⊣
                (   []-monoidal
                 ∘ᵐ mapˣᵐ η⊣ η⊣)
           ∘ᵐ ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        refl
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
          (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       ⟨    ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
         ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ ,
            [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                  ∘ᵐ mapⁱˣᵐ (λ op →
                                                      mapⁱˣᵐ (λ τ''' →
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
         ∘ᵐ mapˣᵐ
              η⊣
              (   []-monoidal
               ∘ᵐ mapˣᵐ η⊣ η⊣)
         ∘ᵐ ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
         ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ
          (⟨⟩ᵐ-fstᵐ _ _)
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))))
      (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ
          (⟨⟩ᵐ-fstᵐ _ _)
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _)))))))) ⟩
    ⟨   ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
        [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                              ∘ᵐ mapⁱˣᵐ (λ op →
                                                  mapⁱˣᵐ (λ τ''' →
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
     ∘ᵐ mapˣᵐ
          η⊣
          (   []-monoidal
           ∘ᵐ mapˣᵐ η⊣ η⊣)
     ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      refl
      (∘ᵐ-congʳ (
        begin
             []-monoidal
          ∘ᵐ mapˣᵐ η⊣ ([]-monoidal ∘ᵐ mapˣᵐ η⊣ η⊣)
          ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ mapˣᵐ η⊣ (   []-monoidal
                       ∘ᵐ mapˣᵐ η⊣ η⊣)
          ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong (mapˣᵐ η⊣) (∘ᵐ-assoc _ _ _)))) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ mapˣᵐ η⊣ (   [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                                            ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                       ∘ᵐ η⊣
                       ∘ᵐ mapˣᵐ η⊣ η⊣)
          ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-identityʳ _)
              (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ ⟨ η⊣ ,
                  [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                                    ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
               ∘ᵐ η⊣
               ∘ᵐ mapˣᵐ η⊣ η⊣
               ∘ᵐ ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
            (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congʳ
              (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))))))) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ ⟨ η⊣ ,
                  [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                                    ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
               ∘ᵐ η⊣
               ∘ᵐ ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
            (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (sym (η⊣-nat _))))) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ ⟨ η⊣ ,
                  [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                                    ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
               ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ ⟨ η⊣ , η⊣ ⟩ᵐ)
               ∘ᵐ η⊣ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
            (cong₂ ⟨_,_⟩ᵐ refl (trans (sym (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _)))))) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ ⟨ η⊣ ,
                  [ op-time op ]ᶠ (   ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                                        ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                                   ∘ᵐ ⟨ op-time op ⟩ᶠ ⟨ η⊣ , η⊣ ⟩ᵐ)
               ∘ᵐ η⊣ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ (cong [ op-time op ]ᶠ
            (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _)))
                  (trans (∘ᵐ-congʳ (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-fstᵐ _ _))) ε⊣∘Fη⊣≡id)))
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _)))
                  (trans (∘ᵐ-congʳ (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-sndᵐ _ _))) ε⊣∘Fη⊣≡id))))))))) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ η⊣
          ∘ᵐ ⟨ η⊣ ,
                  [ op-time op ]ᶠ ⟨ idᵐ , idᵐ ⟩ᵐ
               ∘ᵐ η⊣ ⟩ᵐ
        ≡⟨ ∘ᵐ-congʳ (sym (η⊣-nat _)) ⟩
             [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                               ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
          ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ ⟨ η⊣ ,
                                                   [ op-time op ]ᶠ ⟨ idᵐ , idᵐ ⟩ᵐ
                                                ∘ᵐ η⊣ ⟩ᵐ)
          ∘ᵐ η⊣
        ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))) ⟩
             [ op-time op ]ᶠ (   ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ ,
                                   ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                              ∘ᵐ ⟨ op-time op ⟩ᶠ ⟨ η⊣ ,
                                                      [ op-time op ]ᶠ ⟨ idᵐ , idᵐ ⟩ᵐ
                                                   ∘ᵐ η⊣ ⟩ᵐ)
          ∘ᵐ η⊣
        ≡⟨ ∘ᵐ-congˡ (cong [ op-time op ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (⟨⟩-∘ᵐ _ _))
                (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-fstᵐ _ _)))) ε⊣∘Fη⊣≡id))
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (⟨⟩-∘ᵐ _ _))
                (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-sndᵐ _ _))))
                  (trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
                    (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (ε⊣-nat _)))
                      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ ε⊣∘Fη⊣≡id) (∘ᵐ-identityʳ _))))))))))) ⟩
          [ op-time op ]ᶠ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ
          ∘ᵐ η⊣
        ∎)) ⟩
    ⟨   ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
        [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                              ∘ᵐ mapⁱˣᵐ (λ op →
                                                  mapⁱˣᵐ (λ τ''' →
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
     ∘ᵐ [ op-time op ]ᶠ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ
     ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨  handle-perform-sound-aux8 {Γ} {A} {B} {τ} {τ'} op V M H N  ⟩
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
