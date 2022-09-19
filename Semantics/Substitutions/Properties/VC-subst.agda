-----------------------------------------------------------------------
-- Relating syntactic substitutions to semantic morphism composition --
-----------------------------------------------------------------------

open import Semantics.Model

module Semantics.Substitutions.Properties.VC-subst (Mod : Model) where

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Substitutions

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Semantics.Properties.split-env Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

mutual

  V-subst : ∀ {Γ A B τ}
          → (V : Γ ⊢V⦂ B)
          → (x : A ∈[ τ ] Γ)
          → (W : proj₁ (var-split x) ⊢V⦂ A)
          → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
          ≡    ⟦ V ⟧ᵛᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  V-subst (var y) x W = {!!}
  V-subst (const c) x W = 
    begin
         constᵐ c
      ∘ᵐ terminalᵐ
    ≡⟨ ∘ᵐ-congʳ (sym terminalᵐ-unique) ⟩
         constᵐ c
      ∘ᵐ terminalᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (constᵐ c ∘ᵐ terminalᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst ⋆ x W = 
    begin
      terminalᵐ
    ≡⟨ sym terminalᵐ-unique ⟩
         terminalᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst (lam M) x W = {!!}
  V-subst (box V) x W = {!!}


  C-subst : ∀ {Γ A C τ}
          → (M : Γ ⊢C⦂ C)
          → (x : A ∈[ τ ] Γ)
          → (W : proj₁ (var-split x) ⊢V⦂ A)
          → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ
          ≡    ⟦ M ⟧ᶜᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  C-subst (return V) x W = 
    begin
         ηᵀ
      ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-subst V x W) ⟩
         ηᵀ
      ∘ᵐ ⟦ V ⟧ᵛᵗ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst (M ; N) x W = {!!}
  C-subst (V · V') x W = {!!}
  C-subst (absurd V) x W = 
    begin
         initialᵐ
      ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-subst V x W) ⟩
         initialᵐ
      ∘ᵐ ⟦ V ⟧ᵛᵗ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst (perform op V M) x W = {!!}
  C-subst (handle M `with H `in M₁) x W = {!!}
  C-subst (unbox p V M) x W = {!!}
  C-subst (delay τ M) x W = {!!}
