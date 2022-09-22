--------------------------------------------------------------------------
-- Environment splitting morphisms interaction with weakening renamings --
--------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.split-env-wk-ren (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

split-env-wk-ren : ∀ {Γ Γ' A}
                 → (f : ⟦ Γ ⟧ᵉ →ᵐ ⟦ A ⟧ᵛ)
                 →  ⟦ cong-ren {Γ'' = Γ'} wk-ren ⟧ʳ
                 ∘ᵐ split-env⁻¹ {Γ' = Γ ∷ A} {Γ'' = Γ'} (≡-split refl)
                 ∘ᵐ ⟦ Γ' ⟧ᵉᶠ ⟨ idᵐ , f ⟩ᵐ
                 ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
                 ≡ idᵐ

split-env-wk-ren {Γ} {[]} {A} f = 
  begin
    fstᵐ ∘ᵐ idᵐ ∘ᵐ ⟨ idᵐ , f ⟩ᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
    fstᵐ ∘ᵐ ⟨ idᵐ , f ⟩ᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityʳ _) ⟩
    fstᵐ ∘ᵐ ⟨ idᵐ , f ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-fstᵐ _ _ ⟩
    idᵐ
  ∎
split-env-wk-ren {Γ} {Γ' ∷ B} {A} f = 
  begin
       mapˣᵐ ⟦ cong-ren {Γ'' = Γ'} wk-ren ⟧ʳ idᵐ
    ∘ᵐ mapˣᵐ (split-env⁻¹ {Γ' = Γ ∷ A} {Γ'' = Γ'} (≡-split refl)) idᵐ
    ∘ᵐ mapˣᵐ (⟦ Γ' ⟧ᵉᶠ ⟨ idᵐ , f ⟩ᵐ) idᵐ
    ∘ᵐ mapˣᵐ (split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)) idᵐ
  ≡⟨ trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))))
      (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _))) ⟩
       mapˣᵐ
         (   ⟦ cong-ren {Γ'' = Γ'} wk-ren ⟧ʳ
          ∘ᵐ split-env⁻¹ {Γ' = Γ ∷ A} {Γ'' = Γ'} (≡-split refl)
          ∘ᵐ ⟦ Γ' ⟧ᵉᶠ ⟨ idᵐ , f ⟩ᵐ
          ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl))
         (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
  ≡⟨ cong₂ mapˣᵐ
      (split-env-wk-ren {Γ} {Γ'} f)
      (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) ⟩
    mapˣᵐ idᵐ idᵐ
  ≡⟨ mapˣᵐ-identity ⟩
    idᵐ
  ∎
split-env-wk-ren {Γ} {Γ' ⟨ τ ⟩} {A} f = 
  begin
       ⟨ τ ⟩ᶠ ⟦ cong-ren {Γ'' = Γ'} wk-ren ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ ∷ A} {Γ'' = Γ'} (≡-split refl))
    ∘ᵐ ⟨ τ ⟩ᶠ (⟦ Γ' ⟧ᵉᶠ ⟨ idᵐ , f ⟩ᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl))
  ≡⟨ sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))) ⟩
    ⟨ τ ⟩ᶠ (   ⟦ cong-ren {Γ'' = Γ'} wk-ren ⟧ʳ
            ∘ᵐ split-env⁻¹ {Γ' = Γ ∷ A} {Γ'' = Γ'} (≡-split refl)
            ∘ᵐ ⟦ Γ' ⟧ᵉᶠ ⟨ idᵐ , f ⟩ᵐ
            ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl))
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env-wk-ren {Γ} {Γ'} f) ⟩
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎
