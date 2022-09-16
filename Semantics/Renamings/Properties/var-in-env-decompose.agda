----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.var-in-env-decompose (Mod : Model) where

open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

var-in-env-decompose : ∀ {Γ A τ}
                     → (x : A ∈[ τ ] Γ)
                     → var-in-env x
                    ≡ᵗ    sndᵗ
                       ∘ᵗ ε-⟨⟩ {(⟦ proj₁ (var-split x) ⟧ᵉᵒ 𝟙ᵗ ×ᵗ ⟦ A ⟧ᵛ)}
                       ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
                       ∘ᵗ split-env (proj₁ (proj₂ (proj₂ (var-split x))))
var-in-env-decompose {Γ ∷ A} {.A} {.0} Hd = 
  begin
    sndᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityʳ _) ⟩
       sndᵗ
    ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym ⟨⟩-η⁻¹∘η≡id) ⟩
       sndᵗ
    ∘ᵗ η⁻¹
    ∘ᵗ η {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityˡ _))) ⟩
       sndᵗ
    ∘ᵗ η⁻¹
    ∘ᵗ idᵗ
    ∘ᵗ η {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-≤-refl))) ⟩
       sndᵗ
    ∘ᵗ η⁻¹
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} ≤-refl
    ∘ᵗ η {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _))))) ⟩
       sndᵗ
    ∘ᵗ η⁻¹
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
    ∘ᵗ η {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
       sndᵗ
    ∘ᵗ (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ η {⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
  ≡⟨⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ η
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityʳ _))) ⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ η
    ∘ᵗ idᵗ
  ∎
var-in-env-decompose {Γ ∷ B} {A} {τ} (Tl-∷ x) = 
  begin
       var-in-env x
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (var-in-env-decompose x) ⟩
       ((   sndᵗ
         ∘ᵗ ε-⟨⟩
         ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
         ∘ᵗ split-env (proj₁ (proj₂ (proj₂ (var-split x))))))
    ∘ᵗ fstᵗ
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ
      (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)))) ⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
    ∘ᵗ split-env (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩ᵗ-fstᵗ _ _)))) ⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
    ∘ᵗ fstᵗ
    ∘ᵗ mapˣᵗ (split-env (proj₁ (proj₂ (proj₂ (var-split x))))) idᵗ
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _))) ⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ (   env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
        ∘ᵗ fstᵗ)
    ∘ᵗ mapˣᵗ (split-env (proj₁ (proj₂ (proj₂ (var-split x))))) idᵗ
  ∎
var-in-env-decompose {Γ ⟨ τ ⟩} {A} {.(τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) = 
  begin
       ε-⟨⟩
    ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ (cong ⟨ τ ⟩ᶠ (≡ᵗ-≡ (var-in-env-decompose x)))) ⟩
       ε-⟨⟩
    ∘ᵗ ⟨ τ ⟩ᶠ (   sndᵗ
               ∘ᵗ ε-⟨⟩
               ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
               ∘ᵗ split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congʳ
      (≡ᵗ-trans
        (⟨⟩-∘ᵗ _ _)
        (∘ᵗ-congʳ (
          ≡ᵗ-trans
            (⟨⟩-∘ᵗ _ _)
            (∘ᵗ-congʳ (⟨⟩-∘ᵗ _ _))))) ⟩
       ε-⟨⟩
    ∘ᵗ ⟨ τ ⟩ᶠ sndᵗ
    ∘ᵗ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ sndᵗ
    ∘ᵗ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
       (   (η⁻¹ ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ ⟨ τ ⟩ᶠ sndᵗ)
    ∘ᵗ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-assoc _ _ _) ⟩
       (   η⁻¹
        ∘ᵗ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ ⟩ᶠ sndᵗ)
    ∘ᵗ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congˡ (
      ≡ᵗ-trans
        (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-≤-nat _ _)))
        (≡ᵗ-trans
          (≡ᵗ-sym (∘ᵗ-assoc _ _ _))
          (≡ᵗ-trans
            (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-η⁻¹-nat _)))
            (∘ᵗ-assoc _ _ _)))) ⟩
       (   sndᵗ
        ∘ᵗ η⁻¹
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       (   sndᵗ
        ∘ᵗ η⁻¹
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ (   η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
               ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-trans (∘ᵗ-congˡ (⟨⟩-∘ᵗ _ _)) (∘ᵗ-assoc _ _ _)) ⟩
       (   sndᵗ
        ∘ᵗ η⁻¹
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       sndᵗ
    ∘ᵗ η⁻¹
    ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
    ∘ᵗ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
    ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (
      begin
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
        ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityˡ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
        ∘ᵗ idᵗ
        ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-trans (∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-μ⁻¹∘μ≡id)) (∘ᵗ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ})
        ∘ᵗ μ⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵗ-congʳ (≡ᵗ-trans (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) (∘ᵗ-congˡ ⟨⟩-Tη⁻¹∘ᵗμ⁻¹≡id)) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ≡ᵗ-trans (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) (∘ᵗ-congˡ (⟨⟩-≤-trans _ _)) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ ⟩ᶠ ((⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n))
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵗ-congʳ
          (≡ᵗ-trans
            (≡ᵗ-sym (∘ᵗ-assoc _ _ _))
            (≡ᵗ-trans
              (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-μ-≤₂ _)))
              (∘ᵗ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (+-monoʳ-≤ τ z≤n)
        ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ≡ᵗ-trans
          (≡ᵗ-sym (∘ᵗ-assoc _ _ _))
          (≡ᵗ-trans
            (∘ᵗ-congˡ (⟨⟩-≤-trans _ _))
            (≡ᵗ-trans
              (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _)))
              (∘ᵗ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
        ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ∎)) ⟩
       sndᵗ
    ∘ᵗ η⁻¹
    ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n
    ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
       sndᵗ
    ∘ᵗ (   η⁻¹
        ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _))))) ⟩
       sndᵗ
    ∘ᵗ ε-⟨⟩
    ∘ᵗ (   ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
        ∘ᵗ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ}
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))))
      ∘ᵗ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ∎
