-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux5 (Mod : Model) where

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

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod


handle-perform-sound-aux5 : ∀ {Γ A B τ τ'} → (op : Op)
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
                                                              ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
                                  ∘ᵐ []-monoidal
                                  ∘ᵐ mapˣᵐ
                                      ([ op-time op ]ᶠ idᵐ)
                                      ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                        ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                        ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
                                  ∘ᵐ mapˣᵐ
                                       idᵐ
                                       ([ op-time op ]ᶠ (mapˣᵐ
                                                           ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                           (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ)))
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

handle-perform-sound-aux5 {Γ} {A} {B} {τ} {τ'} op V M H N =
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
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ mapˣᵐ
               ([ op-time op ]ᶠ idᵐ)
               ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                 ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                 ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ mapˣᵐ
                idᵐ
                ([ op-time op ]ᶠ (mapˣᵐ
                                    ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                    (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ)))
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congʳ
      (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
        (cong₂ mapˣᵐ
          (∘ᵐ-identityʳ _)
          (trans (sym ([]-∘ᵐ _ _)) (cong [ op-time op ]ᶠ
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))))))) ⟩
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
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ mapˣᵐ
               ([ op-time op ]ᶠ idᵐ)
               ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                 ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                 ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                 ∘ᵐ mapˣᵐ
                                      ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                      (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ)))
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ
      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _))))))) ⟩
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
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ
                                idᵐ
                                (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                 ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                 ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                 ∘ᵐ mapˣᵐ
                                      ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                      (   map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
                                       ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ)))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl
      (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (   curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                       ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                        (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                         ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                    ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                    ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                       ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                          ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                          ∘ᵐ ×ᵐ-assoc
                                          ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)))
                               ∘ᵐ mapˣᵐ
                                    idᵐ
                                    (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                     ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                     ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                     ∘ᵐ mapˣᵐ
                                          ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                          (   map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
                                           ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ)))
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
      (cong [ op-time op ]ᶠ (trans (sym (curryᵐ-nat _ _)) (cong curryᵐ
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))))) ⟩
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
                                               (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                                ∘ᵐ mapˣᵐ
                                                     ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                     (   map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
                                                      ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ)))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (curryᵐ-nat _ _)))))
          refl))))))))))) ⟩
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
                                               (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                ∘ᵐ curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                                           ∘ᵐ mapˣᵐ
                                                                (mapˣᵐ
                                                                  ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                                  (   map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
                                                                   ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ))
                                                                idᵐ)))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (∘ᵐ-congʳ (∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congʳ
              (cong₂ mapˣᵐ
                (cong₂ mapˣᵐ refl (trans (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)))
                  (sym (curryᵐ-mapˣᵐ _ _ _))))
                refl))))))
          refl))))))))))) ⟩
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
                                               (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                ∘ᵐ curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                                           ∘ᵐ mapˣᵐ
                                                                (mapˣᵐ
                                                                  ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                                  (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                                                           ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)))))
                                                                idᵐ)))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (∘ᵐ-congʳ (∘ᵐ-congʳ (cong curryᵐ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (sym (∘ᵐ-assoc _ _ _))
                  (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-assoc _ _ _)))))
                refl))))))
          refl))))))))))) ⟩
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
                                               (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                ∘ᵐ curryᵐ ⟨    ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                            ∘ᵐ fstᵐ
                                                            ∘ᵐ fstᵐ ,
                                                               uncurryᵐ sndᵐ
                                                            ∘ᵐ mapˣᵐ
                                                                 (mapˣᵐ
                                                                   ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                                   (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                                                            ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)))))
                                                                 idᵐ ⟩ᵐ))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ ⟨_,_⟩ᵐ
          (∘ᵐ-congˡ (cong₂ mapˣᵐ
            refl
            (∘ᵐ-congʳ (∘ᵐ-congʳ (cong curryᵐ
              (cong₂ ⟨_,_⟩ᵐ
                refl
                (sym (uncurryᵐ-nat _ _))))))))
          refl))))))))))) ⟩
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
                                               (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                ∘ᵐ curryᵐ ⟨    ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                            ∘ᵐ fstᵐ
                                                            ∘ᵐ fstᵐ ,
                                                               uncurryᵐ (   sndᵐ
                                                                         ∘ᵐ mapˣᵐ
                                                                              ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                                              (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                                                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))))) ⟩ᵐ))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (trans (∘ᵐ-congʳ (sym (curryᵐ-map⇒ᵐ _ _))) (sym (curryᵐ-map⇒ᵐ _ _))))
          refl))))))))))) ⟩
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
                                               (curryᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ ⟨   ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                            ∘ᵐ fstᵐ
                                                            ∘ᵐ fstᵐ ,
                                                               uncurryᵐ (   sndᵐ
                                                                         ∘ᵐ mapˣᵐ
                                                                              ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                                              (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                                                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))))) ⟩ᵐ)))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (cong uncurryᵐ (⟨⟩ᵐ-sndᵐ _ _)))))))
          refl))))))))))) ⟩
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
                                               (curryᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ ⟨   ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                            ∘ᵐ fstᵐ
                                                            ∘ᵐ fstᵐ ,
                                                               uncurryᵐ (   (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                                                                     ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))))
                                                                         ∘ᵐ sndᵐ) ⟩ᵐ)))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (uncurryᵐ-nat _ _))))))
          refl))))))))))) ⟩
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
                                               (curryᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ ⟨   ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                                            ∘ᵐ fstᵐ
                                                            ∘ᵐ fstᵐ ,
                                                               uncurryᵐ (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                                                                 ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op))))
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (sym (∘ᵐ-assoc _ _ _))
                (trans (∘ᵐ-congˡ T-idᵐ) (trans (∘ᵐ-identityˡ _) (trans (sym (∘ᵐ-assoc _ _ _))
                  (∘ᵐ-congˡ (sym (curryᵐ-uncurryᵐ-iso _)))))))))))))
          refl))))))))))) ⟩
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
                                               (curryᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ mapˣᵐ
                                                             ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ))
                                                             (Tᶠ idᵐ)
                                                        ∘ᵐ ⟨   η⊣
                                                            ∘ᵐ fstᵐ
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (cong curryᵐ
              (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym
                (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (cong₂ ⟨_,_⟩ᵐ
                    (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (η⊣-nat _)) (∘ᵐ-assoc _ _ _))))
                    refl))))))))
          refl))))))))))) ⟩
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
                                               (curryᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ mapˣᵐ
                                                             ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ))
                                                             (Tᶠ idᵐ)
                                                        ∘ᵐ ⟨   [ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ)
                                                            ∘ᵐ η⊣
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
              (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))
                refl))))))))
          refl))))))))))) ⟩
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
                                               (curryᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
                                                        ∘ᵐ strᵀ
                                                        ∘ᵐ mapˣᵐ
                                                             ([ τ ]ᶠ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ))
                                                             (Tᶠ idᵐ)
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
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (cong₂ mapˣᵐ
            refl
            (cong curryᵐ
              (trans (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _))))
                (sym (trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
          refl))))))))))) ⟩
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
  ≡⟨ {!!} ⟩
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

