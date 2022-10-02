-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform (Mod : Model) where

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

handle-perform-sound : ∀ {Γ A B τ τ'} → (op : Op)
                     → (V : Γ ⊢V⦂ type-of-gtype (param op))
                     → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                     → (H : (op : Op) (τ'' : Time)
                          → Γ ∷ type-of-gtype (param op) ∷
                             [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                               ⊢C⦂ B ‼ (op-time op + τ''))
                     → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                     → ⟦ handle perform op V M `with H `in N ⟧ᶜᵗ
                     ≡ ⟦ τ-subst (sym (+-assoc (op-time op) τ τ'))
                           ((H op (τ + τ') [ Tl-∷ Hd ↦ V ]c)
                              [ Hd ↦ box (lam (handle M
                                               `with (λ op' τ'' → C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren ∘ʳ id-ren)))
                                                                    (H op' τ''))
                                               `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N))) ]c) ⟧ᶜᵗ

handle-perform-sound {Γ} {A} {B} {τ} {τ'} V M H N =
  ?
