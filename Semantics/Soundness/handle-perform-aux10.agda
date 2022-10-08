-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux10 (Mod : Model) where

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


handle-perform-sound-aux10 : ∀ {Γ A B τ τ'} → (op : Op)
                           → (V : Γ ⊢V⦂ type-of-gtype (param op))
                           → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                           → (H : (op : Op) (τ'' : Time)
                                → Γ ∷ type-of-gtype (param op) ∷
                                   [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                     ⊢C⦂ B ‼ (op-time op + τ''))
                           → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                           →  τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
                           ∘ᵐ uncurryᵐ idᵐ
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                                             ∘ᵐ ×ᵐ-assoc))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
                           ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ ⟨    (  (  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                          ∘ᵐ curryᵐ (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                      ∘ᵐ projᵐ (τ + τ'))
                                   ∘ᵐ projᵐ op)
                                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ
                                ∘ᵐ fstᵐ ,
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
                              τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
                           ∘ᵐ uncurryᵐ idᵐ
                           ∘ᵐ (  mapˣᵐ (curryᵐ (   (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                                                ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))))) idᵐ
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

handle-perform-sound-aux10 {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨    (  (  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                   ∘ᵐ curryᵐ (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
               ∘ᵐ projᵐ (τ + τ'))
            ∘ᵐ projᵐ op)
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ
         ∘ᵐ fstᵐ ,
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong₂ ⟨_,_⟩ᵐ
        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵢᵐ-projᵐ _ op))))
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵢᵐ-projᵐ _ (τ + τ')))))
            (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))
        refl))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨    (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
             ∘ᵐ curryᵐ (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
         ∘ᵐ fstᵐ ,
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong₂ ⟨_,_⟩ᵐ
        (trans (∘ᵐ-assoc _ _ _) (sym (curryᵐ-mapˣᵐ _ _ _)))
        refl))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ curryᵐ (   (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                 ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ (   mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                          ∘ᵐ ×ᵐ-assoc))))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
        ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ ⟨ curryᵐ (   (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))))
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
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
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
                                  (sym (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _)
                                    (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (sym
                                      (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                        (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                          (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                            (∘ᵐ-identityʳ _)))))))))))))))
                                  (∘ᵐ-identityˡ _)))))))))))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ (  mapˣᵐ (curryᵐ (   (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                         ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))))) idᵐ
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
  ∎

