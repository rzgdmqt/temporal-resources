-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Semantics.Model

module Semantics.Renamings.Core (Mod : Model) where

open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod

open import Util.Equality
open import Util.Time

open Model Mod

-- Semantics of renamings as maps between environments

⟦_⟧ʳ : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → {A : Obj} → ⟦ Γ' ⟧ᵉᵒ A →ᵐ ⟦ Γ ⟧ᵉᵒ A
⟦ id-ren ⟧ʳ =
  idᵐ
⟦ ρ' ∘ʳ ρ ⟧ʳ =
  ⟦ ρ ⟧ʳ ∘ᵐ ⟦ ρ' ⟧ʳ
⟦ wk-ren ⟧ʳ =
  fstᵐ
⟦ var-ren {Γ = Γ} x ⟧ʳ =
  ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ ⟧ᵉᶠ terminalᵐ ⟩ᵐ
⟦ ⟨⟩-η-ren ⟧ʳ =
  η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ =
  η⁻¹
⟦ ⟨⟩-μ-ren {Γ} {τ} {τ'} ⟧ʳ {A} =
  ⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ {⟦ Γ ⟧ᵉᵒ A}
⟦ ⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} ⟧ʳ {A} =
  μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
⟦ ⟨⟩-≤-ren p ⟧ʳ =
  ⟨⟩-≤ p
⟦ cong-∷-ren ρ ⟧ʳ =
  mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
⟦ cong-⟨⟩-ren {τ = τ} ρ ⟧ʳ =
  ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ


-- Semantics of renamings is a natural transformation

postulate
  ⟦⟧ʳ-nat : ∀ {Γ Γ' A B}
          → (ρ : Ren Γ Γ')
          → (f : A →ᵐ B)
          → ⟦ Γ ⟧ᵉᶠ f ∘ᵐ ⟦ ρ ⟧ʳ
          ≡ ⟦ ρ ⟧ʳ ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f
        
-- ⟦⟧ʳ-nat ρ f = {!!}
