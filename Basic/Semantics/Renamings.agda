-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Function

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Semantics.TSets
open import Semantics.Modality.Past
open import Semantics.Interpretation

open import Util.Operations
open import Util.Time

module Semantics.Renamings where

-- Semantics of renamings as maps between environments

⟦_⟧ʳ : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → ⟦ Γ' ⟧ᵉ →ᵗ ⟦ Γ ⟧ᵉ
⟦_⟧ʳ {[]} ρ =
  terminalᵗ
⟦_⟧ʳ {Γ ∷ A} ρ with ren-map ρ Hd
... | τ , p , y =
  ⟨ ⟦_⟧ʳ {Γ} (ρ ∘ʳ wk-ren) , ε-⟨⟩ ∘ᵗ var-in-env y ⟩ᵗ
⟦_⟧ʳ {Γ ⟨ τ ⟩} ρ with split-ren ρ (split-⟨⟩ split-[]) ≤-refl
... | Γ₁' , Γ₂' , ρ' , p , q =
  ⟨ τ ⟩ᶠ ⟦ ρ' ⟧ʳ ∘ᵗ ⟨⟩-≤ {A = ⟦ Γ₁' ⟧ᵉ} q ∘ᵗ split-env-⟨⟩ p
