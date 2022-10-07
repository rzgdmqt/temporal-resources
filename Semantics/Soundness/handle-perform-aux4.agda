-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux4 (Mod : Model) where

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

open import Semantics.Soundness.handle-perform-aux5 Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod


handle-perform-sound-aux4 : ∀ {Γ A B τ τ'} → (op : Op)
                          → (V : Γ ⊢V⦂ type-of-gtype (param op))
                          → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                          → (H : (op : Op) (τ'' : Time)
                               → Γ ∷ type-of-gtype (param op) ∷
                                  [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                    ⊢C⦂ B ‼ (op-time op + τ''))
                          → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                          →   ×ᵐ-assoc⁻¹
                           ∘ᵐ ⟨ fstᵐ ,
                                ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                                  ∘ᵐ fstᵐ
                                  ∘ᵐ sndᵐ ,
                                     [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                              ∘ᵐ mapˣᵐ
                                                                   (   mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                                           ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                                      ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                                                      ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                                                   idᵐ
                                                              ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                              ∘ᵐ ×ᵐ-assoc
                                                              ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
                                  ∘ᵐ []-monoidal
                                  ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                                           (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                                           (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                            ∘ᵐ []-monoidal
                                            ∘ᵐ mapˣᵐ δ idᵐ
                                            ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                                          ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
                           ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
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

handle-perform-sound-aux4 {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                       ∘ᵐ mapˣᵐ
                                            (   mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                               ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                               ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                            idᵐ
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _)))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
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
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
        (cong (mapˣᵐ (idᵐ ∘ᵐ idᵐ)) (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))
            (sym (trans (∘ᵐ-congˡ (trans ([]-∘ᵐ _ _) (∘ᵐ-congʳ ([]-∘ᵐ _ _))))
              (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
                (sym (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))))))))))))))) (∘ᵐ-assoc _ _ _)))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
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
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵛ-⟦⟧ᵍ (param op)) ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                                               ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                                               ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ
          (trans (⟨⟩ᵐ-fstᵐ _ _) (sym (⟨⟩ᵐ-fstᵐ _ _)))
          (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))))) (sym
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (sym (∘ᵐ-assoc _ _ _))
                    (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-congˡ (trans (∘ᵐ-congˡ (sym (⟦⟧ᵛ-⟦⟧ᵍ-iso (param op)))) (∘ᵐ-assoc _ _ _))) (∘ᵐ-assoc _ _ _)))))))))
              (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                  (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                    (cong₂ ⟨_,_⟩ᵐ
                      (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                        (trans (⟨⟩ᵐ-fstᵐ _ _) (sym (⟨⟩ᵐ-fstᵐ _ _)))))))
                      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                        (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
                          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                            (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))))))))))))))))))))))))))))))) (∘ᵐ-assoc _ _ _))) ⟩
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
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                              ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _))
        (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
              (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _))) )))
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
              (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                (cong₂ ⟨_,_⟩ᵐ
                  (trans (∘ᵐ-congˡ []-idᵐ) (trans (∘ᵐ-identityˡ _) (sym
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)))))))
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
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ mapˣᵐ
               ([ op-time op ]ᶠ idᵐ)
               ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                           ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                           ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym
      (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (cong₂ ⟨_,_⟩ᵐ refl
        (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ refl (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congˡ (trans (cong (mapˣᵐ (δ ∘ᵐ η⊣)) (sym (∘ᵐ-identityˡ _))) (mapˣᵐ-∘ᵐ _ _ _ _)))
              (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                (sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (cong₂ ⟨_,_⟩ᵐ
                    (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _))))
                    (∘ᵐ-identityˡ _))))))))))))))))))))))))) ⟩
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
               ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                           ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                           ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ (δ ∘ᵐ η⊣) idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (cong₂ mapˣᵐ refl
      (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (sym η⊣-μ-δ) refl)))) ))) ⟩
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
               ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                           ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                           ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ ([ op-time op ]ᶠ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) ∘ᵐ [ op-time op ]ᶠ η⊣ ∘ᵐ η⊣) idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (cong₂ mapˣᵐ refl (∘ᵐ-congʳ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
        (cong₂ mapˣᵐ
          (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (sym (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-assoc _ _ _)))))
          (trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-identityˡ _) (sym ([]-∘ᵐ _ _)))))))))))))) ⟩
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
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   []-monoidal
                     ∘ᵐ mapˣᵐ
                          ([ op-time op ]ᶠ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣))
                          ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ))
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (cong₂ mapˣᵐ refl
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
           ∘ᵐ []-monoidal
           ∘ᵐ mapˣᵐ
               ([ op-time op ]ᶠ idᵐ)
               ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
                                 ∘ᵐ map⇒ᵐ idᵐ strᵀ
                                 ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ ⟨    η⊣
                ∘ᵐ fstᵐ ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (mapˣᵐ
                                           ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ η⊣)
                                           (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ))
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ idᵐ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (⟨⟩ᵐ-fstᵐ _ _) (trans (∘ᵐ-identityˡ _)
          (sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)))))))
        (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                  (trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _)) (sym (trans (∘ᵐ-assoc _ _ _)
                    (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
                      (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _))))))))))))
              (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
                (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _)
                  (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                    (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                      (cong₂ ⟨_,_⟩ᵐ
                        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-assoc _ _ _)
                            (∘ᵐ-congʳ (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _))))))))))
                        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                          (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
                            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _)
                              (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                                (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
                                  (∘ᵐ-assoc _ _ _))))))))))))))))))))))))))))))))))))
            (∘ᵐ-assoc _ _ _))))))) ⟩
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
  ≡⟨ handle-perform-sound-aux5 {Γ} {A} {B} {τ} {τ'} op V M H N ⟩
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
