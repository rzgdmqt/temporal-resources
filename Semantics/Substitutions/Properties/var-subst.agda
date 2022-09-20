-----------------------------------------------------------------------
-- Relating syntactic substitutions to semantic morphism composition --
-----------------------------------------------------------------------

open import Semantics.Model

module Semantics.Substitutions.Properties.var-subst (Mod : Model) where

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Substitutions

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Semantics.Interpretation.Properties.split-env-isomorphism Mod
open import Semantics.Interpretation.Properties.split-env-naturality Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

var-subst : ∀ {Γ A B τ τ'}
          → (y : B ∈[ τ' ] Γ)
          → (x : A ∈[ τ ] Γ)
          → (W : proj₁ (var-split x) ⊢V⦂ A)
          → ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
          ≡    var-in-env y
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

var-subst Hd Hd W = 
  begin
    ⟦ W ⟧ᵛᵗ
  ≡⟨ sym (⟨⟩ᵐ-sndᵐ _ _) ⟩
    sndᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)) ⟩
    sndᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
    sndᵐ ∘ᵐ idᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ
  ∎
var-subst Hd (Tl-∷ x) W with var-split x
... | Γ₁ , Γ₂ , p , q = 
  begin
    sndᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ ∘ᵐ sndᵐ
  ≡⟨ sym (⟨⟩ᵐ-sndᵐ _ _) ⟩
       sndᵐ
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _)) ⟩
       (idᵐ ∘ᵐ sndᵐ)
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
       (   sndᵐ
        ∘ᵐ ⟨ ⟦ Γ₂ ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       sndᵐ
    ∘ᵐ ⟨ ⟦ Γ₂ ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _)) ⟩
       (idᵐ ∘ᵐ sndᵐ)
    ∘ᵐ ⟨ ⟦ Γ₂ ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
       (   sndᵐ
        ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ ⟦ Γ₂ ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       sndᵐ
    ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟦ Γ₂ ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = Γ₁} {Γ'' = Γ₂} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ∎
var-subst (Tl-∷ y) Hd W = 
  begin
    var-in-env y
  ≡⟨ sym (∘ᵐ-identityʳ _) ⟩
    var-in-env y ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
    var-in-env y ∘ᵐ fstᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (var-in-env y ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)) ⟩
    (var-in-env y ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
    (var-in-env y ∘ᵐ fstᵐ) ∘ᵐ idᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ
  ∎
var-subst (Tl-∷ y) (Tl-∷ x) W = {!!}
var-subst (Tl-⟨⟩ y) x W = {!!}
