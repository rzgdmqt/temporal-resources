------------------------
-- Equality renamings --
------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.eq-ren (Mod : Model) where

open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Util.Equality

open Model Mod

eq-ren-refl : ∀ {Γ A}
            → ⟦ eq-ren {Γ} refl ⟧ʳ {A} ≡ idᵐ
            
eq-ren-refl = 
  begin
    idᵐ
  ≡⟨⟩
    idᵐ
  ∎


eq-ren-trans : ∀ {Γ Γ' Γ'' A}
             → (p : Γ ≡ Γ')
             → (q : Γ' ≡ Γ'')
             → ⟦ eq-ren p ⟧ʳ ∘ᵐ ⟦ eq-ren q ⟧ʳ
             ≡ ⟦ eq-ren (trans p q) ⟧ʳ {A}
             
eq-ren-trans refl refl = 
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎


eq-ren-symˡ : ∀ {Γ Γ' A}
            → (p : Γ ≡ Γ')
            → ⟦ eq-ren (sym p) ⟧ʳ {A} ∘ᵐ ⟦ eq-ren p ⟧ʳ
            ≡ idᵐ
            
eq-ren-symˡ refl =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎


eq-ren-symʳ : ∀ {Γ Γ' A}
            → (p : Γ ≡ Γ')
            → ⟦ eq-ren p ⟧ʳ {A} ∘ᵐ ⟦ eq-ren (sym p) ⟧ʳ
            ≡ idᵐ
            
eq-ren-symʳ refl =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
