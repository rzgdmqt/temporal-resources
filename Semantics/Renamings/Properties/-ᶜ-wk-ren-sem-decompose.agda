---------------------------------------------------
-- Smenatics of context minus weakening renaming --
---------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.-ᶜ-wk-ren-sem-decompose (Mod : Model) where

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

postulate
  ⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ : ∀ {Γ τ}
                          → (p : τ ≤ ctx-time Γ)
                          → ⟦ -ᶜ-wk-ren {Γ} τ ⟧ʳ ≡ ε-⟨⟩ ∘ᵐ env-⟨⟩-ᶜ τ p
                       
--⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ p = {!!}

