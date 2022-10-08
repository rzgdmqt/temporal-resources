-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux8 (Mod : Model) where

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


handle-perform-sound-aux8 : ∀ {Γ A B τ τ'} → (op : Op)
                          → (V : Γ ⊢V⦂ type-of-gtype (param op))
                          → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                          → (H : (op : Op) (τ'' : Time)
                               → Γ ∷ type-of-gtype (param op) ∷
                                  [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                    ⊢C⦂ B ‼ (op-time op + τ''))
                          → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                          →   ⟨   ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
                              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                                    ∘ᵐ mapⁱˣᵐ (λ op →
                                                                        mapⁱˣᵐ (λ τ''' →
                                                                           (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                            ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ
                                                                                       ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
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

handle-perform-sound-aux8 {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
    ⟨   ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
        [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                              ∘ᵐ mapⁱˣᵐ (λ op →
                                                  mapⁱˣᵐ (λ τ''' →
                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                 ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ
                                                                 ∘ᵐ ×ᵐ-assoc⁻¹))))
                                              ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
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
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      refl
      (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))))  ⟩
    ⟨  ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
       [ op-time op ]ᶠ (   curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                   ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ
                                                                   ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
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
                                               idᵐ ⟩ᵐ ⟩ᵐ)
                         ∘ᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ)
    ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ (cong [ op-time op ]ᶠ
      (trans (sym (curryᵐ-nat _ _)) (cong curryᵐ
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))))) ⟩
    ⟨  ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
       [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                             ∘ᵐ mapⁱˣᵐ (λ op →
                                                 mapⁱˣᵐ (λ τ''' →
                                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                     ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ
                                                                ∘ᵐ ×ᵐ-assoc⁻¹))))
                                             ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
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
                                            idᵐ ⟩ᵐ ⟩ᵐ
                                ∘ᵐ mapˣᵐ (⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ) idᵐ))
    ∘ᵐ η⊣ ⟩ᵐ              
  ≡⟨ cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ
      (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))))))) ⟩
    ⟨  ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
       [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                             ∘ᵐ mapⁱˣᵐ (λ op →
                                                 mapⁱˣᵐ (λ τ''' →
                                                    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                     ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ
                                                                ∘ᵐ ×ᵐ-assoc⁻¹))))
                                             ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                     ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                ∘ᵐ mapˣᵐ idᵐ strᵀ
                                ∘ᵐ ⟨    fstᵐ
                                     ∘ᵐ mapˣᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ idᵐ ,
                                        ⟨    η⊣
                                          ∘ᵐ sndᵐ
                                          ∘ᵐ fstᵐ ,
                                             ⟦ M ⟧ᶜᵗ
                                          ∘ᵐ mapˣᵐ (sndᵐ ∘ᵐ sndᵐ) idᵐ ⟩ᵐ
                                     ∘ᵐ mapˣᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ idᵐ ⟩ᵐ))
    ∘ᵐ η⊣ ⟩ᵐ              
  ≡⟨ cong₂ ⟨_,_⟩ᵐ refl
      (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (
        begin
             uncurryᵐ (   T-alg-of-handlerᵀ
                       ∘ᵐ mapⁱˣᵐ (λ op →
                           mapⁱˣᵐ (λ τ''' →
                              (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                               ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                          ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ
                                          ∘ᵐ ×ᵐ-assoc⁻¹))))
                       ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
          ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                               ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
          ∘ᵐ mapˣᵐ idᵐ strᵀ
          ∘ᵐ ⟨    fstᵐ
               ∘ᵐ mapˣᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ idᵐ ,
                  ⟨    η⊣
                    ∘ᵐ sndᵐ
                    ∘ᵐ fstᵐ ,
                       ⟦ M ⟧ᶜᵗ
                    ∘ᵐ mapˣᵐ (sndᵐ ∘ᵐ sndᵐ) idᵐ ⟩ᵐ
               ∘ᵐ mapˣᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ idᵐ ⟩ᵐ
        ≡⟨ {!!} ⟩
             uncurryᵐ (   T-alg-of-handlerᵀ
                       ∘ᵐ mapⁱˣᵐ (λ op →
                           mapⁱˣᵐ (λ τ''' →
                              (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                               ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                          ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                          ∘ᵐ ×ᵐ-assoc⁻¹
                                          ∘ᵐ mapˣᵐ fstᵐ idᵐ))))
                       ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
          ∘ᵐ mapˣᵐ idᵐ (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                               ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
          ∘ᵐ mapˣᵐ idᵐ strᵀ
          ∘ᵐ ⟨    fstᵐ
               ∘ᵐ mapˣᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ idᵐ ,
                  ⟨    η⊣
                    ∘ᵐ sndᵐ
                    ∘ᵐ fstᵐ ,
                       ⟦ M ⟧ᶜᵗ
                    ∘ᵐ mapˣᵐ (sndᵐ ∘ᵐ sndᵐ) idᵐ ⟩ᵐ
               ∘ᵐ mapˣᵐ ⟨ idᵐ , ⟨ idᵐ , idᵐ ⟩ᵐ ⟩ᵐ idᵐ ⟩ᵐ
        ≡⟨ {!!} ⟩
             uncurryᵐ (   T-alg-of-handlerᵀ
                       ∘ᵐ mapⁱˣᵐ (λ op →
                           mapⁱˣᵐ (λ τ''' →
                              (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                               ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                          ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                          ∘ᵐ ×ᵐ-assoc⁻¹
                                          ∘ᵐ mapˣᵐ fstᵐ idᵐ))))
                       ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
          ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                            ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
          ∘ᵐ mapˣᵐ idᵐ strᵀ
          ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ≡⟨ {!!} ⟩
             uncurryᵐ (   T-alg-of-handlerᵀ
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
          ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ∎)))) ⟩
    ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
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
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
      ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (sym (trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (∘ᵐ-identityʳ _)))
      (sym (∘ᵐ-identityˡ _)) ⟩
    ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ ,
         idᵐ
      ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
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
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
      ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) ⟩
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

