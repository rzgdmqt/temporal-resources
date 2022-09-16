-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Semantics.Model

module Semantics.Renamings.Core (Mod : Model) where

open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod

open import Util.Time

open Model Mod

-- Semantics of renamings as maps between environments

⟦_⟧ʳ : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → ⟦ Γ' ⟧ᵉ →ᵗ ⟦ Γ ⟧ᵉ
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
⟦ ⟨⟩-μ-ren {Γ} {τ} {τ'} ⟧ʳ =
  ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ')) ∘ᵗ μ {A = ⟦ Γ ⟧ᵉ}
⟦ ⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} ⟧ʳ =
  μ⁻¹ {⟦ Γ ⟧ᵉ} ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ' τ))
⟦ ⟨⟩-≤-ren {Γ} p ⟧ʳ =
  ⟨⟩-≤ {⟦ Γ ⟧ᵉ} p
⟦ cong-∷-ren ρ ⟧ʳ =
  mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
⟦ cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ ⟧ʳ =
  ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ

