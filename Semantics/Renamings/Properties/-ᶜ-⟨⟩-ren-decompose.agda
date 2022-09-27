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

⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ : ∀ {Γ τ A}
                        → (p : τ ≤ ctx-time Γ)
                        → ⟦ -ᶜ-⟨⟩-ren {Γ} τ p ⟧ʳ {A}
                        ≡ env-⟨⟩-ᶜ τ p
                       
⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ {Γ} {zero} {A} p = 
  begin
    η
  ≡⟨⟩
    η
  ∎
⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ {Γ ∷ B} {suc τ} {A} p = 
  begin
       ⟦ -ᶜ-⟨⟩-ren {Γ = Γ} (suc τ) p ⟧ʳ
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ {Γ} {suc τ} p) ⟩
       env-⟨⟩-ᶜ {Γ = Γ} (suc τ) p
    ∘ᵐ fstᵐ
  ∎
⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} {suc τ} {A} p with suc τ ≤? τ'
... | yes q = 
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (suc τ) (τ' ∸ suc τ))))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m∸n+n≡m q))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (suc τ) (τ' ∸ suc τ)))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m∸n+n≡m q))
  ≡⟨ ∘ᵐ-congʳ (trans (⟨⟩-≤-trans _ _) (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q = 
  begin
       (   ⟨⟩-≤ (≤-reflexive (sym (m∸n+n≡m (≰⇒≥ ¬q))))
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (suc τ ∸ τ') τ'))
        ∘ᵐ μ)
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ -ᶜ-⟨⟩-ren (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) ⟧ʳ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (sym (m∸n+n≡m (≰⇒≥ ¬q))))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (suc τ ∸ τ') τ'))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ -ᶜ-⟨⟩-ren (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
      (⟦-ᶜ-⟨⟩-ren⟧ʳ≡env-⟨⟩-ᶜ {Γ} {suc τ ∸ τ'} (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))))) ⟩
       ⟨⟩-≤ (≤-reflexive (sym (m∸n+n≡m (≰⇒≥ ¬q))))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (suc τ ∸ τ') τ'))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (⟨⟩-≤-trans _ _) (cong ⟨⟩-≤ (≤-irrelevant _ _)))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎
