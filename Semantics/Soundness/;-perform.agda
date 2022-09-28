-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.;-perform (Mod : Model) where

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

;-perform-sound : ∀ {Γ A B τ τ'}
                → (op : Op)
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                → ⟦ perform op V M ; N ⟧ᶜᵗ
                ≡ ⟦ τ-subst (sym (+-assoc (op-time op) τ τ'))
                      (perform op V (M ; C-rename (cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} wk-ren ∘ʳ cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren) N)) ⟧ᶜᵗ

;-perform-sound {Γ} {A} {B} {τ} {τ'} op V M N = 
  begin
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ ⟨ η⊣ ,
            opᵀ op
         ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                 [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
              ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
              ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans
      (cong₂ ⟨_,_⟩ᵐ
        (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _))))
        (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))) (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ strᵀ
    ∘ᵐ mapˣᵐ idᵐ (opᵀ op)
    ∘ᵐ ⟨ η⊣ ,
         ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op))
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ opᵀ op
    ∘ᵐ mapˣᵐ
         idᵐ
         (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ∘ᵐ []-monoidal
          ∘ᵐ mapˣᵐ δ idᵐ)
    ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ η⊣ ,
         ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (opᵀ-nat op _))) (∘ᵐ-assoc _ _ _))) ⟩
       μᵀ
    ∘ᵐ opᵀ op
    ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)))
    ∘ᵐ mapˣᵐ
         idᵐ
         (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ∘ᵐ []-monoidal
          ∘ᵐ mapˣᵐ δ idᵐ)
    ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ η⊣ ,
         ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (opᵀ-algebraicity op))
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ opᵀ op
    ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ μᵀ))
    ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)))
    ∘ᵐ mapˣᵐ
         idᵐ
         (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ∘ᵐ []-monoidal
          ∘ᵐ mapˣᵐ δ idᵐ)
    ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ η⊣ ,
         ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
      (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (cong₂ mapˣᵐ (∘ᵐ-identityˡ _)
        (trans (sym ([]-∘ᵐ _ _)) (cong [ op-time op ]ᶠ (sym (map⇒ᵐ-∘ᵐʳ _ _))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ opᵀ op
    ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ)))
    ∘ᵐ mapˣᵐ
         idᵐ
         (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ∘ᵐ []-monoidal
          ∘ᵐ mapˣᵐ δ idᵐ)
    ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ η⊣ ,
         ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
            mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ ⟨ η⊣ ,
             ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                  [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
               ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
               ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
            mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨    (fstᵐ ∘ᵐ sndᵐ)
             ∘ᵐ ⟨ η⊣ ,
                  ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                       [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                    ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                    ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ,
                ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
             ∘ᵐ ⟨ η⊣ ,
                  ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                       [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                    ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                    ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))
          (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ (⟨⟩ᵐ-fstᵐ _ _)
           (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _)))))) ⟩
            mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
             ⟨ η⊣ ,
                  [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
               ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
               ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
      ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
        ⟨   (idᵐ ∘ᵐ fstᵐ)
          ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
               ⟨ η⊣ ,
                    [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                 ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                 ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
          ,
             ((   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                     ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                 ∘ᵐ []-monoidal
                 ∘ᵐ mapˣᵐ δ idᵐ) ∘ᵐ sndᵐ)
          ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
               ⟨ η⊣ ,
                    [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                 ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                 ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ cong₂ ⟨_,_⟩ᵐ
          (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _)))
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))) ⟩
        ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
          ∘ᵐ ⟨ η⊣ ,
                    [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                 ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                 ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
      ≡⟨ cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,_⟩ᵐ
          (begin
              (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                   ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ []-monoidal
                ∘ᵐ mapˣᵐ δ idᵐ)
            ∘ᵐ ⟨ η⊣ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ
          {-
          ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
               [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ δ idᵐ
            ∘ᵐ ⟨ η⊣ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ δ idᵐ
            ∘ᵐ ⟨ η⊣ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (trans
              (cong₂ ⟨_,_⟩ᵐ
                (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                  (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                    (trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (∘ᵐ-identityʳ _))))))
                (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-congʳ
                  (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))))))
                (⟨⟩ᵐ-∘ᵐ _ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ δ idᵐ
            ∘ᵐ mapˣᵐ η⊣ ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ))
            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
            ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
              (trans (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                (trans (cong₂ mapˣᵐ (sym GGμ∘Gη⊣∘η⊣≡δ∘η⊣) (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))))
                  (trans (mapˣᵐ-∘ᵐ _ _ _ _) (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _))))))
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ ([ op-time op ]ᶠ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ))) idᵐ
            ∘ᵐ mapˣᵐ ([ op-time op ]ᶠ η⊣) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ))
            ∘ᵐ mapˣᵐ η⊣ idᵐ
            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
            ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
              (trans (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (sym []-idᵐ))) (sym ([]-monoidal-nat _ _)))) (∘ᵐ-assoc _ _ _)))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) idᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ ([ op-time op ]ᶠ η⊣) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ))
            ∘ᵐ mapˣᵐ η⊣ idᵐ
            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
            ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
              (trans (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _))))) ⟩
          -}
          ≡⟨ {!!} ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ))
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ η⊣ idᵐ
            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
            ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
          ≡⟨ {!!} ⟩ -- collapse maps
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ idᵐ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ))
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ η⊣ idᵐ
            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
            ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
          ≡⟨ {!!} ⟩ -- (A)
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)))
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ η⊣ idᵐ
            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
            ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
              begin
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
                ∘ᵐ []-monoidal
                ∘ᵐ mapˣᵐ η⊣ idᵐ
                ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
                ∘ᵐ (   [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                    ∘ᵐ η⊣)
                ∘ᵐ mapˣᵐ η⊣ idᵐ
                ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ η⊣
                ∘ᵐ mapˣᵐ η⊣ idᵐ
                ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                  (trans (∘ᵐ-congˡ (sym (η⊣-nat _))) (∘ᵐ-assoc _ _ _))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (mapˣᵐ η⊣ idᵐ))
                ∘ᵐ η⊣
                ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                  (trans (∘ᵐ-congˡ (sym (η⊣-nat _))) (∘ᵐ-assoc _ _ _)))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (mapˣᵐ η⊣ idᵐ))
                ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
                ∘ᵐ η⊣
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ {!!} ⟩ -- collapse maps
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ η⊣ idᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (mapˣᵐ η⊣ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
                ∘ᵐ η⊣
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym ([]-∘ᵐ _ _))
                  (cong [ op-time op ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
                    (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (⟨⟩ᵐ-sndᵐ _ _))))))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ η⊣ ∘ᵐ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (mapˣᵐ η⊣ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
                ∘ᵐ η⊣
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym ([]-∘ᵐ _ _))
                  (cong [ op-time op ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                      (trans (sym (⟨⟩-∘ᵐ _ _)) (trans (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩-∘ᵐ _ _)))))))
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (sym (⟨⟩-∘ᵐ _ _))
                      (trans (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩-∘ᵐ _ _))))))))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ η⊣ ∘ᵐ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ η⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ  ,
                                     ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ ([ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)) ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ η⊣
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong₂ ⟨_,_⟩ᵐ
                  (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ ε⊣∘Fη⊣≡id) (∘ᵐ-identityˡ _))))
                  (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (ε⊣-nat _))) (∘ᵐ-assoc _ _ _)))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ η⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ  ,
                                     curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ η⊣
                ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (η⊣-nat _))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ η⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ fstᵐ  ,
                                     curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ sndᵐ ⟩ᵐ
                ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ ⟨ idᵐ , η⊣ ⟩ᵐ)
                ∘ᵐ η⊣
              ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym ([]-∘ᵐ _ _))
                  (cong [ op-time op ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
                    (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (trans (sym (⟨⟩-∘ᵐ _ _)) (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-fstᵐ _ _))))
                      (trans (∘ᵐ-congʳ ⟨⟩-idᵐ) (∘ᵐ-identityʳ _))))
                    (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                      (trans (sym (⟨⟩-∘ᵐ _ _)) (cong ⟨ op-time op ⟩ᶠ (⟨⟩ᵐ-sndᵐ _ _))))))))))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ η⊣ ,
                                     curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ε⊣ ∘ᵐ ⟨ op-time op ⟩ᶠ η⊣ ⟩ᵐ
                ∘ᵐ η⊣
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong ⟨ η⊣ ,_⟩ᵐ (trans (∘ᵐ-congʳ ε⊣∘Fη⊣≡id) (∘ᵐ-identityʳ _))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                ∘ᵐ [ op-time op ]ᶠ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ
                ∘ᵐ η⊣
              ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))) ⟩
                   [ op-time op ]ᶠ (   curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                    ∘ᵐ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ)
                ∘ᵐ η⊣
              ≡⟨ ∘ᵐ-congˡ (cong [ op-time op ]ᶠ (
                  begin
                       curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                    ∘ᵐ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ
                  ≡⟨ sym (curryᵐ-nat _ _) ⟩
                     curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                             ∘ᵐ ⟨ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                  ≡⟨ cong curryᵐ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
                     curryᵐ ⟨   (fstᵐ ∘ᵐ fstᵐ)
                             ∘ᵐ ⟨ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
                                uncurryᵐ sndᵐ
                             ∘ᵐ ⟨ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                  ≡⟨ cong curryᵐ (cong₂ ⟨_,_⟩ᵐ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                      (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))))) refl) ⟩
                     curryᵐ ⟨ η⊣ ∘ᵐ fstᵐ
                             ,
                                uncurryᵐ sndᵐ
                             ∘ᵐ ⟨ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                  ≡⟨ cong curryᵐ (cong ⟨ η⊣ ∘ᵐ fstᵐ ,_⟩ᵐ (sym (uncurryᵐ-nat _ _))) ⟩
                     curryᵐ ⟨ η⊣ ∘ᵐ fstᵐ ,
                              uncurryᵐ (sndᵐ ∘ᵐ ⟨ η⊣ , curryᵐ ⟦ M ⟧ᶜᵗ ⟩ᵐ) ⟩ᵐ
                  ≡⟨ cong curryᵐ (cong ⟨ η⊣ ∘ᵐ fstᵐ ,_⟩ᵐ (cong uncurryᵐ (⟨⟩ᵐ-sndᵐ _ _))) ⟩
                     curryᵐ ⟨ η⊣ ∘ᵐ fstᵐ ,
                              uncurryᵐ (curryᵐ ⟦ M ⟧ᶜᵗ) ⟩ᵐ
                  ≡⟨ cong curryᵐ (cong ⟨ η⊣ ∘ᵐ fstᵐ ,_⟩ᵐ (curryᵐ-uncurryᵐ-iso _)) ⟩
                    curryᵐ ⟨ η⊣ ∘ᵐ fstᵐ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
                  ∎)) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ η⊣ ∘ᵐ fstᵐ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
                ∘ᵐ η⊣
              ≡⟨ ∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (cong ⟨_, ⟦ M ⟧ᶜᵗ ⟩ᵐ (sym (η⊣-nat _))))) ⟩
                   [ op-time op ]ᶠ (curryᵐ ⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ) ∘ᵐ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
                ∘ᵐ η⊣
              ∎))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)))
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ) ∘ᵐ η⊣ ,
                                          ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ {!!} ⟩ -- pull map out
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)
                                        ∘ᵐ ⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ) ∘ᵐ η⊣ ,
                                             ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
              (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
              (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-congˡ T-idᵐ) (∘ᵐ-identityˡ _))))))))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)
                                        ∘ᵐ ⟨ ([ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ,
                                             (Tᶠ idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
              (⟨⟩ᵐ-∘ᵐ _ _ _)))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)
                                        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ)) (Tᶠ idᵐ)
                                        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ {!!} ⟩ -- swap first maps
               [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ idᵐ strᵀ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)
                                        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ)) (Tᶠ idᵐ)
                                        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ {!!} ⟩ -- pull str out underneath curry
               [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   strᵀ
                                        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ)) (Tᶠ idᵐ)
                                        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ)) (Tᶠ idᵐ)
                                        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (trans (sym (∘ᵐ-assoc _ _ _))
              (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _)))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ)
                                        ∘ᵐ strᵀ
                                        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ)) (Tᶠ idᵐ)
                                        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
              (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _))))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   Tᶠ (mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ)
                                        ∘ᵐ Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                        ∘ᵐ strᵀ
                                        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (sym (trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))))) ⟩
               [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                               ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                        ∘ᵐ strᵀ
                                        ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
            ∘ᵐ η⊣
          ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
               (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                                   ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                            ∘ᵐ strᵀ
                                            ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)))
            ∘ᵐ η⊣
          ∎) ⟩
        ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
            (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
             ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                         ∘ᵐ strᵀ
                                         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)))
         ∘ᵐ η⊣ ⟩ᵐ
      ∎))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ opᵀ op
    ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ)))
    ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
            (   [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
             ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                         ∘ᵐ strᵀ
                                         ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _)))
      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
        (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym ([]-∘ᵐ _ _)))
          (trans (sym ([]-∘ᵐ _ _)) (sym (trans (sym ([]-∘ᵐ _ _)) (cong [ op-time op ]ᶠ (sym
            (begin
                 map⇒ᵐ idᵐ (μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ)
              ∘ᵐ map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
              ∘ᵐ curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                         ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
            ≡⟨ {!!} ⟩
            {-
            ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (map⇒ᵐ-∘ᵐ _ _ _ _))
                (cong₂ map⇒ᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))) ⟩
                 map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) (μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ)
              ∘ᵐ curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                         ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
            ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (map⇒ᵐ-∘ᵐ _ _ _ _))
                (cong₂ map⇒ᵐ (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))) ⟩
                 map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
              ∘ᵐ map⇒ᵐ idᵐ (μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ)
              ∘ᵐ curryᵐ (   Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                         ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
            ≡⟨ ∘ᵐ-congʳ (sym (curryᵐ-map⇒ᵐ _ _)) ⟩
                 map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
              ∘ᵐ curryᵐ (   (   μᵀ
                             ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ)
                         ∘ᵐ Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                         ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
            ≡⟨ ∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-assoc _ _ _)) ⟩
                 map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
              ∘ᵐ curryᵐ (   μᵀ
                         ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
                         ∘ᵐ Tᶠ (   mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                         ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
            ≡⟨ ∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))) ⟩
            -}
                 map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ
              ∘ᵐ curryᵐ (   μᵀ
                         ∘ᵐ Tᶠ (   ⟦ N ⟧ᶜᵗ
                                ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                         ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
            ∎)))))))) (∘ᵐ-assoc _ _ _)))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ opᵀ op
    ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
            [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
         ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   μᵀ
                                     ∘ᵐ Tᶠ (   ⟦ N ⟧ᶜᵗ
                                            ∘ᵐ mapˣᵐ (⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) idᵐ
                                            ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ fstᵐ) idᵐ)
                                     ∘ᵐ strᵀ
                                     ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ
      (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (sym (C-rename≡∘ᵐ (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) N))))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ opᵀ op
    ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
            [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
         ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   μᵀ
                                     ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) N ⟧ᶜᵗ
                                     ∘ᵐ strᵀ
                                     ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ perform op V (M ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) N) ⟧ᶜᵗ
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ _ _) ⟩
    ⟦ τ-subst (sym (+-assoc (op-time op) τ τ')) (perform op V (M ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) N)) ⟧ᶜᵗ
  ∎
