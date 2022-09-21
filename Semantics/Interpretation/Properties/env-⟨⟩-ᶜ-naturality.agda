-------------------------------------------------------
-- Naturality of the minus operation on environments --
-------------------------------------------------------

open import Semantics.Model

module Semantics.Interpretation.Properties.env-⟨⟩-ᶜ-naturality (Mod : Model) where

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

-- TODO: finish typing up the proof later

postulate
  env-⟨⟩-ᶜ-nat : ∀ {Γ A B}
               → (τ : Time)
               → (p : τ ≤ ctx-time Γ)
               → (f : A →ᵐ B)
               →    env-⟨⟩-ᶜ {Γ} τ p 
                 ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
               ≡    ⟨ τ ⟩ᶠ (⟦ Γ -ᶜ τ ⟧ᵉᶠ f)
                 ∘ᵐ env-⟨⟩-ᶜ {Γ} τ p 
