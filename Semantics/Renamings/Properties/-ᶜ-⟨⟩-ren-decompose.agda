---------------------------------------------------
-- Semantics of context minus weakening renaming --
---------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.-ᶜ-⟨⟩-ren-decompose (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

postulate
  ⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ : ∀ {Γ τ A}
                        → (p : τ ≤ ctx-time Γ)
                        → ⟦ -ᶜ-⟨⟩-ren {Γ} τ p ⟧ʳ {A}
                        ≡ env-⟨⟩-ᶜ τ p
                       
--⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ {Γ} {τ} {A} p = {!!}
