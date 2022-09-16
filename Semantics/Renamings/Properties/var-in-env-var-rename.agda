----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.var-in-env-var-rename (Mod : Model) where

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

var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ : ∀ {Γ Γ' A τ}
                                      → (ρ : Ren Γ Γ')
                                      → (x : A ∈[ τ ] Γ)
                                      → var-in-env (proj₂ (proj₂ (var-rename ρ x)))
                                     ≡ᵗ var-in-env x ∘ᵗ ⟦ ρ ⟧ʳ
               
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ id-ren x = 
  begin
    var-in-env x
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityʳ _) ⟩
    var-in-env x ∘ᵗ idᵗ
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ (ρ ∘ʳ ρ') x = 
  begin
    var-in-env (proj₂ (proj₂ (var-rename ρ (proj₂ (proj₂ (var-rename ρ' x))))))
  ≡⟨ var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ ρ (proj₂ (proj₂ (var-rename ρ' x))) ⟩
    (var-in-env (proj₂ (proj₂ (var-rename ρ' x)))) ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-congˡ (var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ ρ' x) ⟩
    (var-in-env x ∘ᵗ ⟦ ρ' ⟧ʳ) ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
    var-in-env x ∘ᵗ ⟦ ρ' ⟧ʳ ∘ᵗ ⟦ ρ ⟧ʳ
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ wk-ren x =
  ≡ᵗ-refl
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ (var-ren y) Hd = 
  begin
    var-in-env y
  ≡⟨ ≡ᵗ-sym (⟨⟩ᵗ-sndᵗ _ _) ⟩
    sndᵗ ∘ᵗ ⟨ idᵗ , var-in-env y ⟩ᵗ
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ (var-ren y) (Tl-∷ x) =
  begin
    var-in-env x
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityʳ _) ⟩
    var-in-env x ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩ᵗ-fstᵗ _ _)) ⟩
    var-in-env x ∘ᵗ (fstᵗ ∘ᵗ ⟨ idᵗ , var-in-env y ⟩ᵗ)
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
    (var-in-env x ∘ᵗ fstᵗ) ∘ᵗ ⟨ idᵗ , var-in-env y ⟩ᵗ
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} ⟨⟩-η-ren (Tl-⟨⟩ x) =
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
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} ⟨⟩-η⁻¹-ren x = 
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
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} (⟨⟩-μ-ren {Γ} {τ} {τ'}) (Tl-⟨⟩ x) =
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
            ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ}))
              ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ ∘ᵗ-congˡ
                (begin
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
                ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _)) ⟩
                     (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                      ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-identityʳ τ')))
                  ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
                ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-identityʳ τ'))
                  ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
                ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-μ∘Tη≡id)) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ (   (   μ {⟦ A ⟧ᵛ}
                          ∘ᵗ ⟨ τ' ⟩ᶠ (η {⟦ A ⟧ᵛ}))
                      ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ}))
                ≡⟨ ∘ᵗ-congʳ (∘ᵗ-assoc _ _ _) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ (   μ {⟦ A ⟧ᵛ}
                      ∘ᵗ (   ⟨ τ' ⟩ᶠ (η {⟦ A ⟧ᵛ})
                          ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})))
                ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ
                    (≡ᵗ-trans
                      (≡ᵗ-trans
                        (≡ᵗ-sym (⟨⟩-∘ᵗ _ _))
                        (≡-≡ᵗ (cong ⟨ τ' ⟩ᶠ (≡ᵗ-≡ ⟨⟩-η∘η⁻¹≡id))))
                      (⟨⟩-idᵗ {⟨ 0 ⟩ᵒ ⟦ A ⟧ᵛ}))) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ (μ {⟦ A ⟧ᵛ} ∘ᵗ idᵗ)
                ≡⟨ ∘ᵗ-congʳ (∘ᵗ-identityʳ _) ⟩
                     ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ μ {⟦ A ⟧ᵛ}
                ∎) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ μ {⟦ A ⟧ᵛ})
              ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ μ {⟦ A ⟧ᵛ}
              ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityʳ _))) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ μ {⟦ A ⟧ᵛ}
              ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
              ∘ᵗ idᵗ
            ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym ⟨⟩-≤-refl))) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ μ {⟦ A ⟧ᵛ}
              ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
              ∘ᵗ ⟨⟩-≤ {⟨ τ ⟩ᵒ ⟦ A ⟧ᵛ} ≤-refl
            ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-μ-≤ _ _)) ⟩
                 ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
              ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-mono-≤ {τ'} {τ'} {0} {τ} ≤-refl z≤n)
              ∘ᵗ μ {⟦ A ⟧ᵛ}
            ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
                 (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
                  ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-mono-≤ {τ'} {τ'} {0} {τ} ≤-refl z≤n))
              ∘ᵗ μ {⟦ A ⟧ᵛ}
            ≡⟨ ∘ᵗ-congˡ (⟨⟩-≤-trans _ _) ⟩
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
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} (⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'}) (Tl-⟨⟩ (Tl-⟨⟩ x)) = 
  begin
       ε-⟨⟩
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       η⁻¹
    ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (
      begin
        ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
      ≡⟨ ≡ᵗ-sym
          (≡ᵗ-trans
            (∘ᵗ-congʳ (∘ᵗ-congʳ (⟨⟩-≤-trans _ _)))
            (≡ᵗ-trans
              (∘ᵗ-congʳ (⟨⟩-≤-trans _ _))
              (⟨⟩-≤-trans _ _))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-monoʳ-≤ τ' z≤n)
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-Tη⁻¹∘ᵗμ⁻¹≡id)) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ (   ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
            ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-monoʳ-≤ τ' z≤n)
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵗ-congʳ (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵗ (   μ⁻¹ {⟦ A ⟧ᵛ}
            ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (+-monoʳ-≤ τ' z≤n))
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ (⟨⟩-μ⁻¹-≤₂ _))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵗ (   ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
            ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ})
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ (⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ}) ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n))
        ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-∘ᵗ _ _))) ⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ' ⟩ᶠ (η⁻¹ {⟦ A ⟧ᵛ} ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ≡⟨⟩
           ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
        ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
      ∎)) ⟩
       η⁻¹
    ∘ᵗ (   ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
        ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ)))
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (≡ᵗ-trans (∘ᵗ-assoc _ _ _)
      (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))) ⟩
       (  (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
       ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
       ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
       ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ)))
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
       (  ε-⟨⟩ {⟦ A ⟧ᵛ}
       ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
       ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
       ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ)))
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _)
      (∘ᵗ-congʳ (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} (≤-reflexive (+-comm τ' τ))
    ∘ᵗ ⟨ τ + τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-≤-nat _ _)))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵗ μ⁻¹ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' + τ ⟩ᶠ (var-in-env x)
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵗ (   μ⁻¹ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ' + τ ⟩ᶠ (var-in-env x))
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-μ⁻¹-nat _)))) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵗ (   ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)) 
        ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ})
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       ε-⟨⟩ {⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)) 
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _))) ⟩
       (   ε-⟨⟩ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ})
        ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (var-in-env x)))
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-∘ᵗ _ _))) ⟩
       (   ε-⟨⟩ {⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (ε-⟨⟩ {⟦ A ⟧ᵛ} ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x)))
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} (⟨⟩-≤-ren {Γ} {τ} {τ'} p) (Tl-⟨⟩ x) =
  begin
    ε-⟨⟩ ∘ᵗ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
    (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵗ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
    η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n ∘ᵗ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _))) ⟩
    η⁻¹ ∘ᵗ (⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} p) ∘ᵗ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))) ⟩
    (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n) ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} p ∘ᵗ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨⟩
    ε-⟨⟩ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} p ∘ᵗ ⟨ τ' ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-≤-nat _ _)) ⟩
    ε-⟨⟩ ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x) ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} p
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
    (ε-⟨⟩ ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x)) ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} p
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} (cong-∷-ren ρ) Hd =
  begin
    sndᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
    idᵗ ∘ᵗ sndᵗ
  ≡⟨ ≡ᵗ-sym (⟨⟩ᵗ-sndᵗ _ _) ⟩
    sndᵗ ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} (cong-∷-ren ρ) (Tl-∷ x) =
  begin
    var-in-env (proj₂ (proj₂ (var-rename ρ x))) ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ ρ x) ⟩
    (var-in-env x ∘ᵗ ⟦ ρ ⟧ʳ) ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
    var-in-env x ∘ᵗ ⟦ ρ ⟧ʳ ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩ᵗ-fstᵗ _ _)) ⟩
    var-in-env x ∘ᵗ fstᵗ ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
    (var-in-env x ∘ᵗ fstᵗ) ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
  ∎
var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ {A = A} (cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ) (Tl-⟨⟩ x) =
  begin
    ε-⟨⟩ ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env (proj₂ (proj₂ (var-rename ρ x))))
  ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ (cong ⟨ τ ⟩ᶠ (≡ᵗ-≡ (var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ ρ x)))) ⟩
    ε-⟨⟩ ∘ᵗ (⟨ τ ⟩ᶠ (var-in-env x ∘ᵗ ⟦ ρ ⟧ʳ))
  ≡⟨ ∘ᵗ-congʳ (⟨⟩-∘ᵗ _ _) ⟩
    ε-⟨⟩ ∘ᵗ (⟨ τ ⟩ᶠ (var-in-env x) ∘ᵗ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
    (ε-⟨⟩ ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x)) ∘ᵗ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ∎
