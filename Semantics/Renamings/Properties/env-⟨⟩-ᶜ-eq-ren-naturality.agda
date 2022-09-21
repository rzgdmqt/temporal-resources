-------------------------------------------------------
-- Naturality of the minus operation on environments --
-------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-eq-ren-naturality (Mod : Model) where

open import Data.Empty

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

env-⟨⟩-ᶜ-eq-ren-nat : ∀ {Γ Γ' A}
                    → (τ : Time)
                    → (p : τ ≤ ctx-time Γ')
                    → (q : Γ' ≡ Γ)
                    →    env-⟨⟩-ᶜ {Γ'} {A} τ p 
                      ∘ᵐ ⟦ eq-ren q ⟧ʳ
                    ≡    ⟨ τ ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ) q) ⟧ʳ
                      ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (≤-reflexive (cong ctx-time q)))

env-⟨⟩-ᶜ-eq-ren-nat τ p refl = 
  begin
       env-⟨⟩-ᶜ τ p
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    env-⟨⟩-ᶜ τ p
  ≡⟨ cong (env-⟨⟩-ᶜ τ) (≤-irrelevant _ _) ⟩
    env-⟨⟩-ᶜ τ (≤-trans p (≤-reflexive refl))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (≤-reflexive refl))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ τ ⟩ᶠ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (≤-reflexive refl))
  ∎
