-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux2 (Mod : Model) where

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

handle-perform-sound-aux2 : ∀ {Γ A B τ τ'} → (op : Op)
                          → (V : Γ ⊢V⦂ type-of-gtype (param op))
                          → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                          → (H : (op : Op) (τ'' : Time)
                               → Γ ∷ type-of-gtype (param op) ∷
                                  [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                    ⊢C⦂ B ‼ (op-time op + τ''))
                          → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                          →   ×ᵐ-assoc⁻¹
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                                              ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                                              ∘ᵐ ×ᵐ-assoc
                                                                                              ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
                           ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ ⟨ fstᵐ
                                ,
                                   mapˣᵐ
                                     (mapⁱˣᵐ (λ op →
                                        mapⁱˣᵐ (λ τ''' →
                                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                           ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                      ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                     idᵐ
                                ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                                           idᵐ
                                           (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                            ∘ᵐ []-monoidal
                                            ∘ᵐ mapˣᵐ δ idᵐ))
                           ∘ᵐ ⟨ idᵐ , ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                                        ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                                        ⟨    η⊣ ,
                                             [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                          ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                                          ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
                           ≡
                              ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                           ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                           ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                           ∘ᵐ ⟨ idᵐ ,
                                [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                                      ∘ᵐ mapⁱˣᵐ (λ op →
                                                                           mapⁱˣᵐ (λ τ''' →
                                                                              (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                               ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                              ∘ᵐ mapˣᵐ (mapˣᵐ ((idᵐ ∘ᵐ ε-⟨⟩) ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                                         ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                                           ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                                         ∘ᵐ mapˣᵐ idᵐ strᵀ
                                                         ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
                                ∘ᵐ η⊣ ⟩ᵐ

handle-perform-sound-aux2 {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                               ∘ᵐ ×ᵐ-assoc⁻¹)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ ⟨ idᵐ , ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                 ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                 ⟨    η⊣ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (trans
        (cong₂ ⟨_,_⟩ᵐ
          refl
          (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (trans
            (cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-identityˡ _)
              (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (sym
                (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                  (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                    (cong₂ ⟨_,_⟩ᵐ
                      (∘ᵐ-identityˡ _)
                      (∘ᵐ-assoc _ _ _)))))))))))))))
            (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
        (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                               ∘ᵐ ×ᵐ-assoc⁻¹)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
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
  ≡⟨ {!!} ⟩ -- merge map and ⟨ ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ ⟨ fstᵐ
         ,
            ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
         ∘ᵐ mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                               ∘ᵐ ×ᵐ-assoc⁻¹)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ
          (∘ᵐ-identityˡ _)
          (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))))
            (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-sndᵐ _ _)
                  (trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _)) (∘ᵐ-identityˡ _))))))
                (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (cong₂ ⟨_,_⟩ᵐ
                    (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                    (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-sndᵐ _ _)
                      (trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _)) (∘ᵐ-identityˡ _))))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ ⟨ fstᵐ
         ,
            ⟨ fstᵐ ∘ᵐ sndᵐ ,
              ⟨    η⊣
                ∘ᵐ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                         (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                          ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                     ∘ᵐ ×ᵐ-assoc⁻¹)))))
                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                ∘ᵐ fstᵐ
                ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ fstᵐ ,_⟩ᵐ (cong ⟨ fstᵐ ∘ᵐ sndᵐ ,_⟩ᵐ
      (cong ⟨_, sndᵐ ∘ᵐ sndᵐ ⟩ᵐ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (η⊣-nat _))) (∘ᵐ-assoc _ _ _))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ ⟨ fstᵐ
         ,
            ⟨ fstᵐ ∘ᵐ sndᵐ ,
              ⟨    [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                           (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                            ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                ∘ᵐ η⊣
                ∘ᵐ fstᵐ
                ,
                   sndᵐ
                ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ
          (∘ᵐ-identityˡ _)
          (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (∘ᵐ-identityˡ _)
              (∘ᵐ-congʳ (sym
                (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (cong₂ ⟨_,_⟩ᵐ refl
                    (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))))))))) )))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ ⟨ fstᵐ
         ,
            ⟨ fstᵐ ∘ᵐ sndᵐ ,
                 []-monoidal
              ∘ᵐ mapˣᵐ
                   ([ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                           (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                            ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)))
                   ([ op-time op ]ᶠ idᵐ)
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ fstᵐ ,_⟩ᵐ (cong ⟨ fstᵐ ∘ᵐ sndᵐ ,_⟩ᵐ
      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ ⟨ fstᵐ
         ,
            ⟨ fstᵐ ∘ᵐ sndᵐ ,
                 [ op-time op ]ᶠ (mapˣᵐ
                                   (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                           (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                            ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                                   idᵐ)
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
  ≡⟨ ∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityˡ _) refl)) ⟩
       ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
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
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ
      (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong mapⁱˣᵐ
        (fun-ext (λ op → cong mapⁱˣᵐ (fun-ext (λ τ''' → ∘ᵐ-congʳ (cong curryᵐ
          (∘ᵐ-congˡ (∘ᵐ-congʳ (cong₂ mapˣᵐ (cong₂ mapˣᵐ (∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _))) refl) refl))))))))))))))))) ⟩
       ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ((idᵐ ∘ᵐ ε-⟨⟩) ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ mapˣᵐ-identity) (∘ᵐ-identityˡ _))) ⟩
       ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ((idᵐ ∘ᵐ ε-⟨⟩) ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ sym (trans (∘ᵐ-congˡ mapˣᵐ-identity) (∘ᵐ-identityˡ _)) ⟩
       ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ((idᵐ ∘ᵐ ε-⟨⟩) ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ∎
