-----------------------------------------------------------------------
-- Relating syntactic substitutions to semantic morphism composition --
-----------------------------------------------------------------------

open import Semantics.Model

module Semantics.Substitutions.Properties.var-subst (Mod : Model) where

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Semantics.Interpretation.Properties.split-env-isomorphism Mod
open import Semantics.Interpretation.Properties.split-env-naturality Mod

open import Semantics.Renamings.Properties.VC-rename Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

var-subst≡∘ᵐ : ∀ {Γ A B τ τ'}
             → (y : B ∈[ τ' ] Γ)
             → (x : A ∈[ τ ] Γ)
             → (W : proj₁ (var-split x) ⊢V⦂ A)
             → ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
             ≡    var-in-env y
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

var-subst≡∘ᵐ Hd Hd W = 
  begin
    ⟦ W ⟧ᵛᵗ
  ≡⟨ sym (⟨⟩ᵐ-sndᵐ _ _) ⟩
    sndᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)) ⟩
    sndᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
    sndᵐ ∘ᵐ idᵐ ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ idᵐ
  ∎
var-subst≡∘ᵐ Hd (Tl-∷ x) W with var-split x
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
var-subst≡∘ᵐ (Tl-∷ y) Hd W = 
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
var-subst≡∘ᵐ (Tl-∷ {B = A} y) (Tl-∷ {B = B} x) W = 
  begin
    ⟦ V-rename wk-ren (y [ x ↦ W ]var) ⟧ᵛᵗ
  ≡⟨ V-rename≡∘ᵐ wk-ren (y [ x ↦ W ]var)  ⟩
       ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
    ∘ᵐ ⟦ wk-ren {proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x))} {A} ⟧ʳ
  ≡⟨⟩
       ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (var-subst≡∘ᵐ y x W) ⟩
       (   var-in-env y
        ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
        ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
        ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) )
    ∘ᵐ fstᵐ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       var-in-env y
    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)))) ⟩
       var-in-env y
    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
       var-in-env y
    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ (   ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩ᵐ-fstᵐ _ _)))) ⟩
       var-in-env y
    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ (   fstᵐ
        ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ ,
             idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))))) ⟩
       var-in-env y
    ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩ᵐ-fstᵐ _ _))) ⟩
       var-in-env y
    ∘ᵐ (   fstᵐ
        ∘ᵐ ⟨ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))) ∘ᵐ fstᵐ ,
             idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))) ⟩
       (   var-in-env y
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))) ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ∎
var-subst≡∘ᵐ (Tl-⟨⟩ {τ = τ} y) (Tl-⟨⟩ {τ = τ'} x) W = 
  begin
    ⟦ V-rename (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) (y [ x ↦ W ]var) ⟧ᵛᵗ
  ≡⟨ V-rename≡∘ᵐ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) (y [ x ↦ W ]var) ⟩
       ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
    ∘ᵐ ⟦ ⟨⟩-≤-ren {proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x))} z≤n ∘ʳ ⟨⟩-η⁻¹-ren ⟧ʳ
  ≡⟨⟩
       ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congˡ (var-subst≡∘ᵐ y x W) ⟩
       (   var-in-env y
        ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
        ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
        ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   (   var-in-env y
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
        ∘ᵐ η⁻¹)
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _) ⟩
       (   η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ (   var-in-env y
                   ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (   var-in-env y
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-≤-nat _ _) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ ⟨ τ ⟩ᶠ (   var-in-env y
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env y)
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
    ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))    
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _)) ⟩
      (   (   η⁻¹
           ∘ᵐ ⟨⟩-≤ z≤n)
       ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env y))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
    ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
  ∎


