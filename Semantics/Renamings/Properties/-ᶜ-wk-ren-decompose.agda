---------------------------------------------------
-- Semantics of context minus weakening renaming --
---------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.-ᶜ-wk-ren-decompose (Mod : Model) where

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

⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ : ∀ {Γ τ A}
                          → (p : τ ≤ ctx-time Γ)
                          → ⟦ -ᶜ-wk-ren {Γ} τ ⟧ʳ {A}
                          ≡ ε-⟨⟩ ∘ᵐ env-⟨⟩-ᶜ τ p
                       
⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ {Γ} {zero} {A} p = 
  begin
    idᵐ
  ≡⟨ sym ⟨⟩-η⁻¹∘η≡id ⟩
    η⁻¹ ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-identityʳ _)) ⟩
    (η⁻¹ ∘ᵐ idᵐ) ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (sym ⟨⟩-≤-refl)) ⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ ≤-refl) ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
    (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ η
  ∎
⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ {Γ ∷ B} {suc τ} {A} p = 
  begin
       ⟦ -ᶜ-wk-ren {Γ} (suc τ) ⟧ʳ
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ {Γ} {suc τ} p) ⟩
       (ε-⟨⟩ ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) p)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
  ∎
⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} {suc τ} {A} p with suc τ ≤? τ'
... | yes q = 
  begin
    ⟨⟩-≤ (m∸n≤m τ' (suc τ))
  ≡⟨ sym (trans (⟨⟩-≤-trans _ _) (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
       ⟨⟩-≤ (+-monoˡ-≤ (τ' ∸ suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ (τ' ∸ suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-η⁻¹∘μ⁻¹≡id)) ⟩
       η⁻¹
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ (τ' ∸ suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩-μ⁻¹-≤₁ _)) (∘ᵐ-assoc _ _ _))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q = 
  begin
       ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congˡ (⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ _) ⟩
       (   (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
        ∘ᵐ env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _)) (∘ᵐ-assoc _ _ _)))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ ⟨⟩-≤ z≤n
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-≤-nat _ _))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (
      begin
        η⁻¹
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
        idᵐ ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id) ⟩
        (μ ∘ᵐ η) ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
        μ ∘ᵐ η ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congʳ ⟨⟩-η∘η⁻¹≡id ⟩
        μ ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        μ
      ∎))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ μ
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-μ-≤₁ _))) (∘ᵐ-assoc _ _ _)))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ (suc τ ∸ τ') z≤n)
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (⟨⟩-≤-trans _ _) (sym (⟨⟩-≤-trans _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
       η⁻¹
    ∘ᵐ ⟨⟩-≤ z≤n
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎

