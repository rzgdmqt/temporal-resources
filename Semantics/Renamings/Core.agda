-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

module Semantics.Renamings.Core where

open import Function

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Semantics.TSets
open import Semantics.Modality.Past
open import Semantics.Interpretation

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Semantics of renamings as maps between environments

⟦_⟧ʳ : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → {A : TSet} → ⟦ Γ' ⟧ᵉᵒ A →ᵗ ⟦ Γ ⟧ᵉᵒ A
⟦ id-ren ⟧ʳ =
  idᵗ
⟦ ρ' ∘ʳ ρ ⟧ʳ =
  ⟦ ρ ⟧ʳ ∘ᵗ ⟦ ρ' ⟧ʳ
⟦ wk-ren ⟧ʳ =
  fstᵗ
⟦ var-ren x ⟧ʳ =
  ⟨ idᵗ , var-in-env x ⟩ᵗ
⟦ ⟨⟩-η-ren ⟧ʳ =
  η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ =
  η⁻¹
⟦ ⟨⟩-μ-ren {Γ} {τ} {τ'} ⟧ʳ {A} =
     ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (+-comm τ τ'))
  ∘ᵗ μ {A = ⟦ Γ ⟧ᵉᵒ A}
⟦ ⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} ⟧ʳ {A} =
     μ⁻¹ {⟦ Γ ⟧ᵉᵒ A}
  ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (+-comm τ' τ))
⟦ ⟨⟩-≤-ren {Γ} p ⟧ʳ {A} =
  ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} p
⟦ cong-∷-ren ρ ⟧ʳ =
  mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
⟦ cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ ⟧ʳ =
  ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
