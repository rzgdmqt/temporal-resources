-------------------------------------------------
-- Decomposing the variable in environment map --
-------------------------------------------------

open import Semantics.Model

module Semantics.Interpretation.Properties.var-in-env-decompose (Mod : Model) where

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

-- Total time-passage of an environment as a single ⟨_⟩ modality

env-ctx-time-⟨⟩ : (Γ : Ctx)
                → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵐ ⟨ ctx-time Γ ⟩ᵒ A

env-ctx-time-⟨⟩ []            = η
env-ctx-time-⟨⟩ (Γ ∷ A)       = env-ctx-time-⟨⟩ Γ ∘ᵐ fstᵐ
env-ctx-time-⟨⟩ (Γ ⟨ τ ⟩) {A} =
     ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
  ∘ᵐ μ {A}
  ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)

-- Decomposing var-in-env in terms of the context splitting given by variable x

var-in-env-decompose : ∀ {Γ A τ}
                     → (x : A ∈[ τ ] Γ)
                     → var-in-env x
                     ≡    sndᵐ
                       ∘ᵐ ε-⟨⟩ {(⟦ proj₁ (var-split x) ⟧ᵉᵒ 𝟙ᵐ ×ᵐ ⟦ A ⟧ᵛ)}
                       ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
                       ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x))))
                       
var-in-env-decompose {Γ ∷ A} {.A} {.0} Hd = 
  begin
    sndᵐ
  ≡⟨ sym (∘ᵐ-identityʳ _) ⟩
       sndᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym ⟨⟩-η⁻¹∘η≡id) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ idᵐ
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-≤-refl))) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} ≤-refl
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)))) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       sndᵐ
    ∘ᵐ (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ η
    ∘ᵐ idᵐ
  ∎
var-in-env-decompose {Γ ∷ B} {A} {τ} (Tl-∷ x) = 
  begin
       var-in-env x
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (var-in-env-decompose x) ⟩
       ((   sndᵐ
         ∘ᵐ ε-⟨⟩
         ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
         ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x))))))
    ∘ᵐ fstᵐ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
    ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
    ∘ᵐ fstᵐ
    ∘ᵐ mapˣᵐ (split-env (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ (   env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
        ∘ᵐ fstᵐ)
    ∘ᵐ mapˣᵐ (split-env (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ
  ∎
var-in-env-decompose {Γ ⟨ τ ⟩} {A} {.(τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) = 
  begin
       ε-⟨⟩
    ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (var-in-env-decompose x)) ⟩
       ε-⟨⟩
    ∘ᵐ ⟨ τ ⟩ᶠ (   sndᵐ
               ∘ᵐ ε-⟨⟩
               ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
               ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ
      (trans
        (⟨⟩-∘ᵐ _ _)
        (∘ᵐ-congʳ (
          trans
            (⟨⟩-∘ᵐ _ _)
            (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))) ⟩
       ε-⟨⟩
    ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _) ⟩
       (   η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congˡ (
      trans
        (∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)))
        (trans
          (sym (∘ᵐ-assoc _ _ _))
          (trans
            (∘ᵐ-congˡ (sym (⟨⟩-η⁻¹-nat _)))
            (∘ᵐ-assoc _ _ _)))) ⟩
       (   sndᵐ
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       (   sndᵐ
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (   η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
               ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)) ⟩
       (   sndᵐ
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
    ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
        ∘ᵐ idᵐ
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (sym ⟨⟩-μ⁻¹∘μ≡id)) (∘ᵐ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
        ∘ᵐ μ⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-Tη⁻¹∘μ⁻¹≡id)) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩-≤-trans _ _)) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ ((⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n))
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ
          (trans
            (sym (∘ᵐ-assoc _ _ _))
            (trans
              (∘ᵐ-congˡ (sym (⟨⟩-μ-≤₂ _)))
              (∘ᵐ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (+-monoʳ-≤ τ z≤n)
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ trans
          (sym (∘ᵐ-assoc _ _ _))
          (trans
            (∘ᵐ-congˡ (⟨⟩-≤-trans _ _))
            (trans
              (∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)))
              (∘ᵐ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ∎)) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       sndᵐ
    ∘ᵐ (   η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ (   ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))))
      ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ∎
