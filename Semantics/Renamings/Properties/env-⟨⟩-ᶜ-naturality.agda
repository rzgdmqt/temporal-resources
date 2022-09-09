----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-naturality where

open import Function

open import Data.Product

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

env-⟨⟩-ᶜ-nat : ∀ {Γ Γ'}
             → (τ : Time)
             → (p : τ ≤ ctx-time Γ)
             → (ρ : Ren Γ Γ')
             →    env-⟨⟩-ᶜ {Γ} τ p
               ∘ᵗ ⟦ ρ ⟧ʳ
            ≡ᵗ    ⟨ τ ⟩ᶠ ⟦ ρ -ʳ τ ⟧ʳ
               ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ))
env-⟨⟩-ᶜ-nat zero p ρ = 
  begin
    η ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ≡ᵗ-sym (⟨⟩-η-nat _) ⟩
    ⟨ zero ⟩ᶠ ⟦ ρ ⟧ʳ ∘ᵗ η
  ∎
env-⟨⟩-ᶜ-nat {Γ ∷ A} {Γ'} (suc τ) p ρ =
  begin
    (env-⟨⟩-ᶜ {Γ} (suc τ) p ∘ᵗ fstᵗ) ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
    env-⟨⟩-ᶜ {Γ} (suc τ) p ∘ᵗ (fstᵗ ∘ᵗ ⟦ ρ ⟧ʳ)
  ≡⟨⟩
    env-⟨⟩-ᶜ {Γ} (suc τ) p ∘ᵗ ⟦ ρ ∘ʳ wk-ren ⟧ʳ
  ≡⟨ env-⟨⟩-ᶜ-nat (suc τ) p (ρ ∘ʳ wk-ren) ⟩
       ⟨ suc τ ⟩ᶠ (idᵗ ∘ᵗ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵗ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans ≤-refl (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong ⟨ suc τ ⟩ᶠ (∘ᵗ-identityˡ _)) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵗ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans ≤-refl (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ {!dcong₂ env-⟨⟩-ᶜ !}) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵗ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p ρ = {!!}
