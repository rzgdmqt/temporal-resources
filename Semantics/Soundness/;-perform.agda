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
                ≡ ⟦ τ-subst (sym (+-assoc (op-time op) τ τ')) (perform op V (M ; C-rename (cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} wk-ren ∘ʳ cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren) N)) ⟧ᶜᵗ

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
  ≡⟨ {!!} ⟩
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
  ≡⟨ sym (τ-subst≡∘ᵐ _ _) ⟩
    ⟦ τ-subst (sym (+-assoc (op-time op) τ τ')) (perform op V (M ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren) ∘ʳ cong-∷-ren ⟨⟩-μ-ren) N)) ⟧ᶜᵗ
  ∎
