----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Interpretation.Properties.var-in-env-var-rename (Mod : Model) where

open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ : ∀ {Γ Γ' A τ}
                                      → (ρ : Ren Γ Γ')
                                      → (x : A ∈[ τ ] Γ)
                                      → var-in-env (proj₂ (proj₂ (var-rename ρ x)))
                                     ≡ var-in-env x ∘ᵐ ⟦ ρ ⟧ʳ
               
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ id-ren x = 
  begin
    var-in-env x
  ≡⟨ sym (∘ᵐ-identityʳ _) ⟩
    var-in-env x ∘ᵐ idᵐ
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ (ρ ∘ʳ ρ') x = 
  begin
    var-in-env (proj₂ (proj₂ (var-rename ρ (proj₂ (proj₂ (var-rename ρ' x))))))
  ≡⟨ var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ ρ (proj₂ (proj₂ (var-rename ρ' x))) ⟩
    (var-in-env (proj₂ (proj₂ (var-rename ρ' x)))) ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ ρ' x) ⟩
    (var-in-env x ∘ᵐ ⟦ ρ' ⟧ʳ) ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
    var-in-env x ∘ᵐ ⟦ ρ' ⟧ʳ ∘ᵐ ⟦ ρ ⟧ʳ
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ wk-ren x =
  refl
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ (var-ren y) Hd = 
  begin
    var-in-env y
  ≡⟨ sym (⟨⟩ᵐ-sndᵐ _ _) ⟩
    sndᵐ ∘ᵐ ⟨ idᵐ , var-in-env y ⟩ᵐ
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ (var-ren y) (Tl-∷ x) =
  begin
    var-in-env x
  ≡⟨ sym (∘ᵐ-identityʳ _) ⟩
    var-in-env x ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
    var-in-env x ∘ᵐ (fstᵐ ∘ᵐ ⟨ idᵐ , var-in-env y ⟩ᵐ)
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (var-in-env x ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , var-in-env y ⟩ᵐ
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} ⟨⟩-η-ren (Tl-⟨⟩ x) =
  begin
    var-in-env x
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ var-in-env x
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-η⁻¹∘η≡id) ⟩
    (η⁻¹ ∘ᵐ η {⟦ A ⟧ᵛ}) ∘ᵐ var-in-env x
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (sym (∘ᵐ-identityʳ _))) ⟩
     ((η⁻¹ ∘ᵐ idᵐ) ∘ᵐ η {⟦ A ⟧ᵛ}) ∘ᵐ var-in-env x
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (sym ⟨⟩-≤-refl))) ⟩
    ((η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} ≤-refl) ∘ᵐ η {⟦ A ⟧ᵛ}) ∘ᵐ var-in-env x
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congʳ (cong ⟨⟩-≤ (≤-irrelevant _ _)))) ⟩
    ((η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵐ η {⟦ A ⟧ᵛ}) ∘ᵐ var-in-env x
  ≡⟨⟩
    (ε-⟨⟩ ∘ᵐ η) ∘ᵐ var-in-env x
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
    ε-⟨⟩ ∘ᵐ (η ∘ᵐ var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-η-nat _)) ⟩
    ε-⟨⟩ ∘ᵐ (⟨ 0 ⟩ᶠ (var-in-env x) ∘ᵐ η)
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (ε-⟨⟩ ∘ᵐ ⟨ 0 ⟩ᶠ (var-in-env x)) ∘ᵐ η
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} ⟨⟩-η⁻¹-ren x = 
  begin
    ε-⟨⟩ ∘ᵐ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} ≤-refl) ∘ᵐ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ ⟨⟩-≤-refl) ⟩
    (η⁻¹ ∘ᵐ idᵐ) ∘ᵐ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-identityʳ _) ⟩
    η⁻¹ ∘ᵐ ⟨ 0 ⟩ᶠ (var-in-env x)
  ≡⟨ sym (⟨⟩-η⁻¹-nat _) ⟩
    var-in-env x ∘ᵐ η⁻¹
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} (⟨⟩-μ-ren {Γ} {τ} {τ'}) (Tl-⟨⟩ x) =
  begin
       ε-⟨⟩
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ} ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩
       ε-⟨⟩
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ} ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ (   ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵐ ⟨ τ' ⟩ᶠ(⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ (   ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
            ∘ᵐ ⟨ τ' ⟩ᶠ(⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ ∘ᵐ-congˡ
      (trans
        (∘ᵐ-assoc _ _ _)
        (trans
          (∘ᵐ-congʳ (
            begin
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
              ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ}))
              ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ ∘ᵐ-congˡ
                (begin
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
                ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)) ⟩
                     (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                      ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-identityʳ τ')))
                  ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
                ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-identityʳ τ'))
                  ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
                ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-μ∘Tη≡id)) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ (   (   μ {⟦ A ⟧ᵛ}
                          ∘ᵐ ⟨ τ' ⟩ᶠ (η {⟦ A ⟧ᵛ}))
                      ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ}))
                ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ (   μ {⟦ A ⟧ᵛ}
                      ∘ᵐ (   ⟨ τ' ⟩ᶠ (η {⟦ A ⟧ᵛ})
                          ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})))
                ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
                    (trans
                      (trans
                        (sym (⟨⟩-∘ᵐ _ _))
                        (cong ⟨ τ' ⟩ᶠ ⟨⟩-η∘η⁻¹≡id))
                      (⟨⟩-idᵐ {⟨ 0 ⟩ᵒ ⟦ A ⟧ᵛ}))) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ (μ {⟦ A ⟧ᵛ} ∘ᵐ idᵐ)
                ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityʳ _) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ μ {⟦ A ⟧ᵛ}
                ∎) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ μ {⟦ A ⟧ᵛ})
              ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ μ {⟦ A ⟧ᵛ}
              ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ μ {⟦ A ⟧ᵛ}
              ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
              ∘ᵐ idᵐ
            ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym ⟨⟩-≤-refl))) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ μ {⟦ A ⟧ᵛ}
              ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
              ∘ᵐ ⟨⟩-≤ {⟨ τ ⟩ᵒ ⟦ A ⟧ᵛ} ≤-refl
            ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-μ-≤ _ _)) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-mono-≤ {τ'} {τ'} {0} {τ} ≤-refl z≤n)
              ∘ᵐ μ {⟦ A ⟧ᵛ}
            ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-mono-≤ {τ'} {τ'} {0} {τ} ≤-refl z≤n))
              ∘ᵐ μ {⟦ A ⟧ᵛ}
            ≡⟨ ∘ᵐ-congˡ (⟨⟩-≤-trans _ _) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ μ {⟦ A ⟧ᵛ}
            ≡⟨⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-trans z≤n (≤-reflexive (+-comm τ τ')))
              ∘ᵐ μ {⟦ A ⟧ᵛ}
            ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ')))
              ∘ᵐ μ {⟦ A ⟧ᵛ}
            ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
              ∘ᵐ μ {⟦ A ⟧ᵛ}
            ∎))
          (sym (∘ᵐ-assoc _ _ _)))) ⟩
       (   (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
        ∘ᵐ μ {⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
    ∘ᵐ μ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x))
  ≡⟨⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
    ∘ᵐ (   μ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-μ-nat _))) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
    ∘ᵐ (   ⟨ τ' + τ ⟩ᶠ (var-in-env x)
        ∘ᵐ μ {⟦ Γ ⟧ᵉ})
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ (   ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ τ'))
        ∘ᵐ ⟨ τ' + τ ⟩ᶠ (var-in-env x))
    ∘ᵐ μ {⟦ Γ ⟧ᵉ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-≤-nat _ _))) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ (   ⟨ τ + τ' ⟩ᶠ (var-in-env x)
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')))
    ∘ᵐ μ {⟦ Γ ⟧ᵉ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ'))
    ∘ᵐ μ {⟦ Γ ⟧ᵉ}
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       ((η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x))
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')) ∘ᵐ μ {⟦ Γ ⟧ᵉ}
  ≡⟨⟩
       (ε-⟨⟩ ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x))
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')) ∘ᵐ μ {⟦ Γ ⟧ᵉ}
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} (⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'}) (Tl-⟨⟩ (Tl-⟨⟩ x)) = 
  begin
       ε-⟨⟩
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (
      begin
        ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
      ≡⟨ sym
          (trans
            (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-≤-trans _ _)))
            (trans
              (∘ᵐ-congʳ (⟨⟩-≤-trans _ _))
              (⟨⟩-≤-trans _ _))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-monoʳ-≤ τ' z≤n)
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-Tη⁻¹∘μ⁻¹≡id)) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ (   ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
            ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-monoʳ-≤ τ' z≤n)
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵐ (   μ⁻¹ {⟦ A ⟧ᵛ}
            ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-monoʳ-≤ τ' z≤n))
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-μ⁻¹-≤₂ _))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵐ (   ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ (⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ}) ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n))
        ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ _ _))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ} ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
        ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ∎)) ⟩
       η⁻¹
    ∘ᵐ (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
        ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ)))
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-assoc _ _ _)
      (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))))) ⟩
       (  (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
       ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
       ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
       ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ)))
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
       (  ε-⟨⟩ {⟦ A ⟧ᵛ}
       ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
       ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
       ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ)))
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ trans (∘ᵐ-assoc _ _ _)
      (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵐ μ⁻¹ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' + τ ⟩ᶠ (var-in-env x)
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵐ (   μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ' + τ ⟩ᶠ (var-in-env x))
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-μ⁻¹-nat _)))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵐ (   ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)) 
        ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ})
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)) 
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
       (   ε-⟨⟩ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)))
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       (   ε-⟨⟩ {⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ} ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x)))
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} (⟨⟩-≤-ren {Γ} {τ} {τ'} p) (Tl-⟨⟩ x) =
  begin
    ε-⟨⟩ ∘ᵐ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵐ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
    η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n ∘ᵐ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _))) ⟩
    η⁻¹ ∘ᵐ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} p) ∘ᵐ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))) ⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} p ∘ᵐ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
    ε-⟨⟩ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} p ∘ᵐ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)) ⟩
    ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x) ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} p
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x)) ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} p
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} (cong-∷-ren ρ) Hd =
  begin
    sndᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ sndᵐ
  ≡⟨ sym (⟨⟩ᵐ-sndᵐ _ _) ⟩
    sndᵐ ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} (cong-∷-ren ρ) (Tl-∷ x) =
  begin
    var-in-env (proj₂ (proj₂ (var-rename ρ x))) ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ ρ x) ⟩
    (var-in-env x ∘ᵐ ⟦ ρ ⟧ʳ) ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
    var-in-env x ∘ᵐ ⟦ ρ ⟧ʳ ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
    var-in-env x ∘ᵐ fstᵐ ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (var-in-env x ∘ᵐ fstᵐ) ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
  ∎
var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ {A = A} (cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ) (Tl-⟨⟩ x) =
  begin
    ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env (proj₂ (proj₂ (var-rename ρ x))))
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ ρ x)) ⟩
    ε-⟨⟩ ∘ᵐ (⟨ τ ⟩ᶠ (var-in-env x ∘ᵐ ⟦ ρ ⟧ʳ))
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩
    ε-⟨⟩ ∘ᵐ (⟨ τ ⟩ᶠ (var-in-env x) ∘ᵐ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x)) ∘ᵐ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ∎
