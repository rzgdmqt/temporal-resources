----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

module Semantics.Renamings.Properties.var-in-env where

open import Function

open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.TSets
open import Semantics.Modality.Past
open import Semantics.Interpretation
open import Semantics.Renamings.Core

open import Util.Equality
open import Util.Operations
open import Util.Time

var-in-env∘ᵗ⟦⟧ʳ : ∀ {Γ Γ' A τ}
                → (ρ : Ren Γ Γ')
                → (x : A ∈[ τ ] Γ)
                → var-in-env (proj₂ (proj₂ (var-rename ρ x)))
               ≡ᵗ var-in-env x ∘ᵗ ⟦ ρ ⟧ʳ
               
var-in-env∘ᵗ⟦⟧ʳ id-ren x = 
  begin
    var-in-env x
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityʳ _) ⟩
    var-in-env x ∘ᵗ idᵗ
  ∎
var-in-env∘ᵗ⟦⟧ʳ (ρ ∘ʳ ρ') x = 
  begin
    var-in-env (proj₂ (proj₂ (var-rename ρ (proj₂ (proj₂ (var-rename ρ' x))))))
  ≡⟨ var-in-env∘ᵗ⟦⟧ʳ ρ (proj₂ (proj₂ (var-rename ρ' x))) ⟩
    (var-in-env (proj₂ (proj₂ (var-rename ρ' x)))) ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-congˡ (var-in-env∘ᵗ⟦⟧ʳ ρ' x) ⟩
    (var-in-env x ∘ᵗ ⟦ ρ' ⟧ʳ) ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
    var-in-env x ∘ᵗ ⟦ ρ' ⟧ʳ ∘ᵗ ⟦ ρ ⟧ʳ
  ∎
var-in-env∘ᵗ⟦⟧ʳ wk-ren x =
  ≡ᵗ-refl
var-in-env∘ᵗ⟦⟧ʳ (var-ren y) Hd = 
  begin
    var-in-env y
  ≡⟨ ≡ᵗ-sym (⟨⟩ᵗ-sndᵗ _ _) ⟩
    sndᵗ ∘ᵗ ⟨ idᵗ , var-in-env y ⟩ᵗ
  ∎
var-in-env∘ᵗ⟦⟧ʳ (var-ren y) (Tl-∷ x) =
  begin
    var-in-env x
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityʳ _) ⟩
    var-in-env x ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩ᵗ-fstᵗ _ _)) ⟩
    var-in-env x ∘ᵗ (fstᵗ ∘ᵗ ⟨ idᵗ , var-in-env y ⟩ᵗ)
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
    (var-in-env x ∘ᵗ fstᵗ) ∘ᵗ ⟨ idᵗ , var-in-env y ⟩ᵗ
  ∎
var-in-env∘ᵗ⟦⟧ʳ {A = A} ⟨⟩-η-ren (Tl-⟨⟩ x) =
  {!!}
{-
  begin
    var-in-env x
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
    idᵗ ∘ᵗ var-in-env x
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-η⁻¹∘η≡id) ⟩
    (η⁻¹ ∘ᵗ η {⟦ A ⟧ᵛ}) ∘ᵗ var-in-env x
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congˡ (≡ᵗ-sym (∘ᵗ-identityʳ _))) ⟩
    ((η⁻¹ ∘ᵗ idᵗ) ∘ᵗ η {⟦ A ⟧ᵛ}) ∘ᵗ var-in-env x
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congˡ (∘ᵗ-congʳ (≡ᵗ-sym ⟨⟩-≤-refl))) ⟩
    ((η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} ≤-refl) ∘ᵗ η {⟦ A ⟧ᵛ}) ∘ᵗ var-in-env x
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congˡ (∘ᵗ-congʳ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _))))) ⟩
    ((η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵗ η {⟦ A ⟧ᵛ}) ∘ᵗ var-in-env x
  ≡⟨⟩
    (ε-⟨⟩ ∘ᵗ η) ∘ᵗ var-in-env x
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
    ε-⟨⟩ ∘ᵗ (η ∘ᵗ var-in-env x)
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-η-nat _)) ⟩
    ε-⟨⟩ ∘ᵗ (⟨ 0 ⟩ᶠ (var-in-env x) ∘ᵗ η)
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
    (ε-⟨⟩ ∘ᵗ ⟨ 0 ⟩ᶠ (var-in-env x)) ∘ᵗ η
  ∎
-}
var-in-env∘ᵗ⟦⟧ʳ {A = A} ⟨⟩-η⁻¹-ren x = 
  begin
    ε-⟨⟩ ∘ᵗ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨⟩
    (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵗ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congʳ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _)))) ⟩
    (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} ≤-refl) ∘ᵗ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congʳ ⟨⟩-≤-refl) ⟩
    (η⁻¹ ∘ᵗ idᵗ) ∘ᵗ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-identityʳ _) ⟩
    η⁻¹ ∘ᵗ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ≡ᵗ-sym (⟨⟩-η⁻¹-nat _) ⟩
    var-in-env x ∘ᵗ η⁻¹
  ∎
var-in-env∘ᵗ⟦⟧ʳ {A = A} (⟨⟩-μ-ren {Γ} {τ} {τ'}) (Tl-⟨⟩ x) =
  begin
       ε-⟨⟩
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ} ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ∘ᵗ-congʳ (⟨⟩-∘ᵗ _ _) ⟩
       ε-⟨⟩
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ} ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (⟨⟩-∘ᵗ _ _)) ⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ (   ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵗ ⟨ τ' ⟩ᶠ(⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n))
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
       (   (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ (   ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
            ∘ᵗ ⟨ τ' ⟩ᶠ(⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)))
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ∘ᵗ-congˡ
      (≡ᵗ-trans
        (∘ᵗ-assoc _ _ _)
        (≡ᵗ-trans
          (∘ᵗ-congʳ (
            begin
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
              ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ {!!} ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ μ {⟦ A ⟧ᵛ}
            ≡⟨⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-trans z≤n (≤-reflexive (+-comm τ τ')))
              ∘ᵗ μ {⟦ A ⟧ᵛ}
            ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _)) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ')))
              ∘ᵗ μ {⟦ A ⟧ᵛ}
            ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
              ∘ᵗ μ {⟦ A ⟧ᵛ}
            ∎))
          (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))) ⟩
       (   (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
        ∘ᵗ μ {⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
    ∘ᵗ μ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
    ∘ᵗ (   μ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-μ-nat _))) ⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
    ∘ᵗ (   ⟨ τ' + τ ⟩ᶠ (var-in-env x)
        ∘ᵗ μ {⟦ Γ ⟧ᵉ})
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ (   ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
        ∘ᵗ ⟨ τ' + τ ⟩ᶠ (var-in-env x))
    ∘ᵗ μ {⟦ Γ ⟧ᵉ}
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-nat _ _))) ⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ (   ⟨ τ + τ' ⟩ᶠ (var-in-env x)
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')))
    ∘ᵗ μ {⟦ Γ ⟧ᵉ}
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-assoc _ _ _) ⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ'))
    ∘ᵗ μ {⟦ Γ ⟧ᵉ}
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
       ((η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x))
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')) ∘ᵗ μ {⟦ Γ ⟧ᵉ}
  ≡⟨⟩
       (ε-⟨⟩ ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x))
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')) ∘ᵗ μ {⟦ Γ ⟧ᵉ}
  ∎
var-in-env∘ᵗ⟦⟧ʳ ⟨⟩-μ⁻¹-ren x = {!!}
var-in-env∘ᵗ⟦⟧ʳ (⟨⟩-≤-ren p) (Tl-⟨⟩ x) = {!!}
var-in-env∘ᵗ⟦⟧ʳ (cong-∷-ren ρ) x = {!!}
var-in-env∘ᵗ⟦⟧ʳ (cong-⟨⟩-ren ρ) x = {!!}
