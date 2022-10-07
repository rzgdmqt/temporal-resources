-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux (Mod : Model) where

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

open import Semantics.Soundness.handle-perform-aux2 Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

handle-perform-sound-aux : ∀ {Γ A B τ τ'} → (op : Op)
                         → (V : Γ ⊢V⦂ type-of-gtype (param op))
                         → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                         → (H : (op : Op) (τ'' : Time)
                              → Γ ∷ type-of-gtype (param op) ∷
                                 [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                   ⊢C⦂ B ‼ (op-time op + τ''))
                         → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                         →    ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
                           ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                                             ∘ᵐ ×ᵐ-assoc))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
                           ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ ⟨ idᵐ
                                ,
                                   mapˣᵐ
                                     (mapⁱˣᵐ (λ op →
                                        mapⁱˣᵐ (λ τ''' →
                                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
                                     idᵐ
                                ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                                           idᵐ
                                           (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                            ∘ᵐ []-monoidal
                                            ∘ᵐ mapˣᵐ δ idᵐ))
                           ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                                        ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                                          ∘ᵐ ⟦ V ⟧ᵛᵗ ,
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

handle-perform-sound-aux {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ (   mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                          ∘ᵐ ×ᵐ-assoc))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
        ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ ⟨ idᵐ
             ,
                mapˣᵐ
                  (mapⁱˣᵐ (λ op →
                     mapⁱˣᵐ (λ τ''' →
                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                        ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
                  idᵐ
             ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))))))
      (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))))
        (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))))
          (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))
            (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
              (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
                (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym
                  (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))))))
                    (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))))
                      (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))))
                        (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))
                          (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
                            (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
                              (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                                (cong₂ ⟨_,_⟩ᵐ
                                  (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _)
                                    (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (sym
                                      (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                        (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                          (∘ᵐ-identityʳ _)))))))))))))))
                                  refl))))))))))))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ (   mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                          ∘ᵐ ×ᵐ-assoc))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
        ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ ⟨ fstᵐ
             ,
                mapˣᵐ
                  (mapⁱˣᵐ (λ op →
                     mapⁱˣᵐ (λ τ''' →
                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                        ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
                  idᵐ
             ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityˡ _) (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))
            (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (⟨⟩ᵐ-fstᵐ _ _)
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _))))))))))))))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
    ∘ᵐ (   mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                          ∘ᵐ ×ᵐ-assoc))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
        (cong₂ mapˣᵐ
          (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))
          (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
            (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
              (cong₂ mapˣᵐ
                (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))
                (sym (trans ([]-∘ᵐ _ _) (∘ᵐ-congʳ ([]-∘ᵐ _ _)))))))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ)
                                              ∘ᵐ curryᵐ (mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc)
                                              ∘ᵐ mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
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
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
      (cong₂ mapˣᵐ
        (∘ᵐ-identityˡ _)
        (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (∘ᵐ-identityʳ _)
            (trans (sym ([]-∘ᵐ _ _)) (cong [ op-time op ]ᶠ
              (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                (trans (sym (map⇒ᵐ-∘ᵐ _ _ _ _)) (trans
                  (cong₂ map⇒ᵐ
                    (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))
                    (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))
                  (map⇒ᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))))))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ)
                                                               ∘ᵐ map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ
                                                               ∘ᵐ curryᵐ (mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc)
                                                               ∘ᵐ mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ fstᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong (mapˣᵐ idᵐ) (cong₂ mapˣᵐ refl (cong [ op-time op ]ᶠ
      (∘ᵐ-congʳ (trans (sym (curryᵐ-mapˣᵐ _ _ _)) (cong curryᵐ (∘ᵐ-assoc _ _ _)))))))) ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ)
                                                               ∘ᵐ curryᵐ (   mapˣᵐ idᵐ appᵐ
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
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong (mapˣᵐ idᵐ) (cong₂ mapˣᵐ refl (cong [ op-time op ]ᶠ
      (sym (curryᵐ-map⇒ᵐ _ _)))))) ⟩
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
  ≡⟨ handle-perform-sound-aux2 op V M H N ⟩
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
