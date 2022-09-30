-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-return (Mod : Model) where

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

handle-return-sound : ∀ {Γ A B τ'}
                    → (V : Γ ⊢V⦂ A)
                    → (H : (op : Op) (τ'' : Time)
                         → Γ ∷ type-of-gtype (param op) ∷
                             [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                               ⊢C⦂ B ‼ (op-time op + τ''))
                    → (N : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ')
                    → ⟦ handle return V `with H `in N ⟧ᶜᵗ
                    ≡ ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟧ᶜᵗ

handle-return-sound {Γ} {A} {B} {τ'} V H N =
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
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
      (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (trans
        (cong₂ ⟨_,_⟩ᵐ
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              (sym (∘ᵐ-identityʳ _)))))))
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
              (begin
                   ηᵀ
                ∘ᵐ ⟦ N ⟧ᶜᵗ
                ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
              ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (ηᵀ-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
                   Tᶠ ⟦ N ⟧ᶜᵗ
                ∘ᵐ ηᵀ
                ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ strᵀ-ηᵀ))) ⟩
                   Tᶠ ⟦ N ⟧ᶜᵗ
                ∘ᵐ strᵀ
                ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
                ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans
                  (cong₂ ⟨_,_⟩ᵐ
                    (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                    (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))))
                  (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
                   Tᶠ ⟦ N ⟧ᶜᵗ
                ∘ᵐ strᵀ
                ∘ᵐ ⟨ ε⁻¹ ∘ᵐ η , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (sym η⊣≡ε⁻¹∘η) refl)) ⟩
                   Tᶠ ⟦ N ⟧ᶜᵗ
                ∘ᵐ strᵀ
                ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
              ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                   (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ)
                ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
              ∎)))))))
        (⟨⟩ᵐ-∘ᵐ _ _ _))))) ⟩
       uncurryᵐ (   T-alg-of-handlerᵀ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
    ∘ᵐ mapˣᵐ idᵐ ηᵀ
    ∘ᵐ ⟨ idᵐ , ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (∘ᵐ-congˡ (uncurryᵐ-nat _ _)) (∘ᵐ-assoc _ _ _) ⟩
       uncurryᵐ T-alg-of-handlerᵀ
    ∘ᵐ mapˣᵐ
         (⟨ (λ op → ⟨ (λ τ''' →
                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                  ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
               ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
         idᵐ
    ∘ᵐ mapˣᵐ idᵐ ηᵀ
    ∘ᵐ ⟨ idᵐ , ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (trans
        (cong₂ mapˣᵐ
          (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
          (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))
      (mapˣᵐ-∘ᵐ _ _ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
       uncurryᵐ T-alg-of-handlerᵀ
    ∘ᵐ mapˣᵐ idᵐ ηᵀ
    ∘ᵐ mapˣᵐ
         (⟨ (λ op → ⟨ (λ τ''' →
                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                  ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
               ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
         idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ T-alg-of-handlerᵀ-ηᵀ) ⟩
       sndᵐ
    ∘ᵐ mapˣᵐ
         (⟨ (λ op → ⟨ (λ τ''' →
                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                  ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
               ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
         idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ η , ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))) (trans (⟨⟩ᵐ-sndᵐ _ _) (trans (∘ᵐ-assoc _ _ _)
      (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-identityˡ _) (∘ᵐ-congʳ (trans
        (cong₂ ⟨_,_⟩ᵐ
          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityʳ _))))
          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _)))))
        (⟨⟩ᵐ-∘ᵐ _ _ _))))))) ⟩
       ⟦ N ⟧ᶜᵗ
    ∘ᵐ ⟨ η ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ η ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (C-rename≡∘ᵐ (cong-∷-ren ⟨⟩-η-ren) N)) ⟩
       ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) N ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) N ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) N ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ sym (C-subst≡∘ᵐ (C-rename (cong-∷-ren ⟨⟩-η-ren) N) Hd V) ⟩
    ⟦ C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟧ᶜᵗ
  ∎

