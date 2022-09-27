-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness (Mod : Model) where

open import Relation.Nullary

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

open import Semantics.Soundness.;-return Mod

open import Semantics.Soundness.·-lam Mod
open import Semantics.Soundness.absurd-eta Mod

open import Semantics.Soundness.delay-; Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

mutual

  V-soundness : ∀ {Γ A}
              → {V W : Γ ⊢V⦂ A}
              → Γ ⊢V⦂ V == W
              → ⟦ V ⟧ᵛᵗ ≡ ⟦ W ⟧ᵛᵗ

  V-soundness {Γ} {A} {V} {.V} V-refl = 
    begin
      ⟦ V ⟧ᵛᵗ
    ≡⟨⟩
      ⟦ V ⟧ᵛᵗ
    ∎
  V-soundness {Γ} {A} {V} {W} (V-sym p) = 
    begin
      ⟦ V ⟧ᵛᵗ
    ≡⟨ sym (V-soundness p) ⟩
      ⟦ W ⟧ᵛᵗ
    ∎
  V-soundness {Γ} {A} {V} {U} (V-trans {W = W} p q) = 
    begin
      ⟦ V ⟧ᵛᵗ
    ≡⟨ V-soundness p ⟩
      ⟦ W ⟧ᵛᵗ
    ≡⟨ V-soundness q ⟩
      ⟦ U ⟧ᵛᵗ
    ∎
  V-soundness {Γ} {.(_ ⇒ _ ‼ _)} {lam M} {lam N} (lam-cong p) = 
    begin
      curryᵐ ⟦ M ⟧ᶜᵗ
    ≡⟨ cong curryᵐ (C-soundness p) ⟩
      curryᵐ ⟦ N ⟧ᶜᵗ
    ∎
  V-soundness {Γ} {[ τ ] A} {box V} {box W} (box-cong p) = 
    begin
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (V-soundness p)) ⟩
      [ τ ]ᶠ ⟦ W ⟧ᵛᵗ ∘ᵐ η⊣
    ∎
  V-soundness {Γ} {.Unit} {.V} {.⋆} (⋆-eta V) = 
    begin
      ⟦ V ⟧ᵛᵗ
    ≡⟨ terminalᵐ-unique ⟩
      terminalᵐ
    ∎
  V-soundness {Γ} {A ⇒ C} {.V} {.(lam (V-rename wk-ren V · var Hd))} (lam-eta V) = 
    begin
      ⟦ V ⟧ᵛᵗ
    ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
         idᵐ
      ∘ᵐ ⟦ V ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congˡ (sym (uncurryᵐ-curryᵐ-iso _)) ⟩
         curryᵐ (uncurryᵐ idᵐ)
      ∘ᵐ ⟦ V ⟧ᵛᵗ
    ≡⟨ sym (curryᵐ-nat _ _) ⟩
      curryᵐ (   uncurryᵐ idᵐ
              ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ≡⟨ cong curryᵐ (∘ᵐ-congʳ (cong ⟨ ⟦ V ⟧ᵛᵗ ∘ᵐ fstᵐ ,_⟩ᵐ (∘ᵐ-identityˡ _))) ⟩
      curryᵐ (   uncurryᵐ idᵐ
              ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ)
    ≡⟨ cong curryᵐ (∘ᵐ-congʳ (cong ⟨_, sndᵐ ⟩ᵐ (sym (V-rename≡∘ᵐ wk-ren V)))) ⟩
      curryᵐ (   uncurryᵐ idᵐ
              ∘ᵐ ⟨ ⟦ V-rename (wk-ren {A = A}) V ⟧ᵛᵗ , sndᵐ ⟩ᵐ)
    ∎

  C-soundness : ∀ {Γ C}
              → {M N : Γ ⊢C⦂ C}
              → Γ ⊢C⦂ M == N
              → ⟦ M ⟧ᶜᵗ ≡ ⟦ N ⟧ᶜᵗ

  C-soundness {Γ} {_} {M} {.M} C-refl = 
    begin
      ⟦ M ⟧ᶜᵗ
    ≡⟨⟩
      ⟦ M ⟧ᶜᵗ
    ∎
  C-soundness {Γ} {_} {M} {N} (C-sym p) = 
    begin
      ⟦ M ⟧ᶜᵗ
    ≡⟨ sym (C-soundness p) ⟩
      ⟦ N ⟧ᶜᵗ
    ∎
  C-soundness {Γ} {_} {M} {P} (C-trans {N = N} p q) = 
    begin
      ⟦ M ⟧ᶜᵗ
    ≡⟨ C-soundness p ⟩
      ⟦ N ⟧ᶜᵗ
    ≡⟨ C-soundness q ⟩
      ⟦ P ⟧ᶜᵗ
    ∎
  C-soundness {Γ} {_} {return V} {return W} (return-cong p) = 
    begin
      ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-soundness p) ⟩
      ηᵀ ∘ᵐ ⟦ W ⟧ᵛᵗ
    ∎
  C-soundness {Γ} {_} {M ; N} {M' ; N'} (;-cong p q) = 
    begin
      μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (C-soundness q))) ⟩
      μᵀ ∘ᵐ Tᶠ ⟦ N' ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ η⊣ ,_⟩ᵐ (C-soundness p)))) ⟩
      μᵀ ∘ᵐ Tᶠ ⟦ N' ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M' ⟧ᶜᵗ ⟩ᵐ
    ∎
  C-soundness {Γ} {_} {V · W} {V' · W'} (·-cong p q) = 
    begin
      uncurryᵐ idᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (V-soundness p) (V-soundness q)) ⟩
      uncurryᵐ idᵐ ∘ᵐ ⟨ ⟦ V' ⟧ᵛᵗ , ⟦ W' ⟧ᵛᵗ ⟩ᵐ
    ∎
  C-soundness {Γ} {_} {absurd V} {absurd W} (absurd-cong p) = 
    begin
      initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-soundness p) ⟩
      initialᵐ ∘ᵐ ⟦ W ⟧ᵛᵗ
    ∎
  C-soundness {Γ} {_} {perform op V M} {perform _ W N} (perform-cong p q) = 
    begin
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ) ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (V-soundness p)) refl) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ W ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ) ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congˡ (
        cong [ op-time op ]ᶠ (cong curryᵐ (C-soundness q)))))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ W ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ N ⟧ᶜᵗ) ∘ᵐ η⊣ ⟩ᵐ
    ∎
  C-soundness {Γ} {_} {handle M `with H `in N} {handle M' `with H' `in N'} (handle-cong p q r) = 
    begin
         uncurryᵐ (   T-alg-of-handlerᵀ
                   ∘ᵐ ⟨   (λ op → ⟨ (λ τ'' →
                            (   curryᵐ
                                  (   idᵐ ∘ᵐ uncurryᵐ idᵐ
                                   ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                           ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                                           ∘ᵐ sndᵐ ⟩ᵐ
                                        ∘ᵐ sndᵐ ⟩ᵐ)
                             ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ'')
             ⟩ᵢᵐ
             ∘ᵐ projᵐ op)
          ⟩ᵢᵐ
          ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → 
        ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' → ∘ᵐ-congˡ (∘ᵐ-congʳ (
          cong curryᵐ (∘ᵐ-congˡ (C-soundness (q op τ'')))))))))))))) ⟩
         uncurryᵐ (   T-alg-of-handlerᵀ
                   ∘ᵐ ⟨   (λ op → ⟨ (λ τ'' →
                            (   curryᵐ
                                  (   idᵐ ∘ᵐ uncurryᵐ idᵐ
                                   ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                           ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                                           ∘ᵐ sndᵐ ⟩ᵐ
                                        ∘ᵐ sndᵐ ⟩ᵐ)
                             ∘ᵐ curryᵐ (⟦ H' op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ'')
             ⟩ᵢᵐ
             ∘ᵐ projᵐ op)
          ⟩ᵢᵐ
          ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ idᵐ ∘ᵐ fstᵐ ,_⟩ᵐ (∘ᵐ-congˡ (cong Tᶠ (C-soundness r))))) ⟩
         uncurryᵐ (   T-alg-of-handlerᵀ
                   ∘ᵐ ⟨   (λ op → ⟨ (λ τ'' →
                            (   curryᵐ
                                  (   idᵐ ∘ᵐ uncurryᵐ idᵐ
                                   ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                           ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                                           ∘ᵐ sndᵐ ⟩ᵐ
                                        ∘ᵐ sndᵐ ⟩ᵐ)
                             ∘ᵐ curryᵐ (⟦ H' op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ'')
             ⟩ᵢᵐ
             ∘ᵐ projᵐ op)
          ⟩ᵢᵐ
          ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N' ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (cong ⟨ η⊣ ,_⟩ᵐ (C-soundness p))))) ⟩
         uncurryᵐ (   T-alg-of-handlerᵀ
                   ∘ᵐ ⟨   (λ op → ⟨ (λ τ'' →
                            (   curryᵐ
                                  (   idᵐ ∘ᵐ uncurryᵐ idᵐ
                                   ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                           ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                                           ∘ᵐ sndᵐ ⟩ᵐ
                                        ∘ᵐ sndᵐ ⟩ᵐ)
                             ∘ᵐ curryᵐ (⟦ H' op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ'')
             ⟩ᵢᵐ
             ∘ᵐ projᵐ op)
          ⟩ᵢᵐ
          ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N' ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M' ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ∎
  C-soundness {Γ} {_} {unbox p V M} {unbox q W N} (unbox-cong {A} {C} {τ} r s) = 
    begin
      ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (C-soundness s) ⟩
      ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ ⟩ᶠ (V-soundness r))))) ⟩
      ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ W ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong (env-⟨⟩-ᶜ τ) (≤-irrelevant _ _))))) ⟩
      ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ W ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ q ⟩ᵐ
    ∎
  C-soundness {Γ} {_} {delay τ M} {delay _ N} (delay-cong p) = 
    begin
      delayᵀ τ ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (C-soundness p))) ⟩
      delayᵀ τ ∘ᵐ [ τ ]ᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ η⊣
    ∎
  C-soundness {Γ} {_} {.(return V ; M)} {.(C-rename (cong-∷-ren ⟨⟩-η-ren) M [ Hd ↦ V ]c)} (;-return V M) =
    ;-return-sound V M
  C-soundness {Γ} {_}
    {.(perform op V M ; N)}
    {.(τ-subst (sym (+-assoc (op-time op) _ _)) (perform op V (M ; C-rename (cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} wk-ren ∘ʳ cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren) N)))}
    (;-perform {A} {B} {τ} {τ'} op V M N) = {!!}
  C-soundness {Γ} {_}
    {.((M ; N) ; P)}
    {.(τ-subst (sym (+-assoc τ τ' τ'')) (M ; (N ; C-rename (cong-ren {Γ'' = [] ⟨ τ' ⟩ ∷ B} wk-ren ∘ʳ cong-ren {Γ'' = [] ∷ B} ⟨⟩-μ-ren) P)))}
    (;-assoc {A} {B} {C} {τ} {τ'} {τ''} M N P) = {!!}
  C-soundness {Γ} {_} {.(lam M · W)} {.(M [ Hd ↦ W ]c)} (·-lam M W) =
    ·-lam-sound M W
  C-soundness {Γ} {_} {.(handle return V `with H `in N)} {.(C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c)} (handle-return V H N) = {!!}
  C-soundness {Γ} {_}
    {.(handle perform op V M `with H `in N)}
    {.(τ-subst (sym (+-assoc (op-time op) _ _))
        ((H op (τ + τ') [ Tl-∷ Hd ↦ V ]c)
           [ Hd ↦ box (lam (handle M `with (λ op' τ'' → C-rename (cong-ren {Γ'' = [] ∷ _ ∷ [ _ ] (_ ⇒ _)} wk-ctx-ren) (H op' τ'')) `in
                    (C-rename (cong-ren {Γ'' = [] ∷ A} (cong-ren {Γ'' = [] ⟨ τ ⟩} wk-ren ∘ʳ ⟨⟩-μ-ren)) N))) ]c))}
    (handle-op {A} {B} {τ} {τ'} op V M H N) = {!!}
  C-soundness {Γ} {_} {_} {.(N [ Hd ↦ V-rename (-ᶜ-⟨⟩-ren _ p) V ]c)} (unbox-box p V N) = {!!}
  C-soundness {Γ} {_} {M} {.(τ-subst (+-identityʳ _) (M ; return (var Hd)))} (;-eta .M) = {!!}
  C-soundness {Γ} {_} {.(absurd V)} {_} (absurd-eta V N) =
    absurd-eta-sound V N
  C-soundness {Γ} {_}
    {.(M [ Hd ↦ V-rename (-ᶜ-wk-ren τ) V ]c)}
    {.(unbox p V (C-rename (exch-ren ∘ʳ wk-ren) M [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c))}
    (box-unbox-eta {A} {C} {τ} p V M) = {!!}
  C-soundness {Γ} {_}
    {.(delay _ M ; N)}
    {.(τ-subst (sym (+-assoc τ τ' τ'')) (delay _ (M ; C-rename (cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren) N)))}
    (delay-; {A} {B} {τ} {τ'} {τ''} M N) =
      delay-;-sound M N
  C-soundness {Γ} {_}
    {.(handle delay _ M `with H `in N)}
    {.(τ-subst (sym (+-assoc τ τ' τ'')) (delay _
      (handle M `with (λ op τ''' → C-rename (cong-ren {Γ'' = [] ∷ _ ∷ _} (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren)) (H op τ''')) `in
        (C-rename (cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren) N))))}
    (delay-handle {A} {B} {τ} {τ'} {τ''} M H N) = {!!}
