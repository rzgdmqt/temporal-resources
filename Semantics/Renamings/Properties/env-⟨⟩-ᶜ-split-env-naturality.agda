-------------------------------------------------------
-- Naturality of the minus operation on environments --
-------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-split-env-naturality (Mod : Model) where

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
  env-⟨⟩-ᶜ-split-env-nat : ∀ {Γ Γ' A}
                         → (τ : Time)
                         → (p : τ ≤ ctx-time Γ')
                         →    env-⟨⟩-ᶜ {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p 
                           ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
                         ≡    ⟨ τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
                           ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
                           ∘ᵐ env-⟨⟩-ᶜ {Γ ++ᶜ Γ'} τ
                                (≤-trans p
                                  (≤-trans
                                    (m≤n+m (ctx-time Γ') (ctx-time Γ))
                                    (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))

postulate
  env-⟨⟩-ᶜ-split-env⁻¹-nat : ∀ {Γ Γ' A}
                           → (τ : Time)
                           → (p : τ ≤ ctx-time Γ')
                           →    env-⟨⟩-ᶜ {Γ ++ᶜ Γ'} {A = A} τ
                                  (≤-trans p
                                    (≤-trans
                                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
                             ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
                           ≡    ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
                             ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
                             ∘ᵐ env-⟨⟩-ᶜ {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p
