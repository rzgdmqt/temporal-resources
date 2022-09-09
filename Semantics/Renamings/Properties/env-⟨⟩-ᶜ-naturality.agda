----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-naturality where

open import Function

open import Data.Product

open import Relation.Nullary

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

-- TODO: finish typing up the proof later

postulate
  env-⟨⟩-ᶜ-nat : ∀ {Γ Γ'}
               → (τ : Time)
               → (p : τ ≤ ctx-time Γ)
               → (ρ : Ren Γ Γ')
               →    env-⟨⟩-ᶜ {Γ} τ p
                 ∘ᵗ ⟦ ρ ⟧ʳ {𝟙ᵗ}
              ≡ᵗ    ⟨ τ ⟩ᶠ ⟦ ρ -ʳ τ ⟧ʳ
                 ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ))
{-
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
  ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ (cong (λ p → env-⟨⟩-ᶜ {Γ'} (suc τ) p {𝟙ᵗ}) (≤-irrelevant _ _))) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵗ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p id-ren with suc τ ≤? τ'
... | yes q = 
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} {suc τ} {τ' ∸ suc τ}
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-identityʳ _ ⟩
       μ⁻¹ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} {suc τ} {τ' ∸ suc τ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (∘ᵗ-identityˡ _)) ⟩
       (   idᵗ
        ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} {suc τ} {τ' ∸ suc τ})
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       idᵗ
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} {suc τ} {τ' ∸ suc τ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
       ⟨ suc τ ⟩ᶠ idᵗ
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} {suc τ} {τ' ∸ suc τ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ 𝟙ᵗ} (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q = 
  begin
    (⟨⟩-≤ (m≤n+m∸n (suc τ) τ') ∘ᵗ
       μ ∘ᵗ
       ⟨ τ' ⟩ᶠ
       (env-⟨⟩-ᶜ (suc τ ∸ τ')
        (≤-trans (∸-monoˡ-≤ τ' p)
         (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
      ∘ᵗ idᵗ
    ≡⟨ {!!} ⟩
      ⟨ suc τ ⟩ᶠ idᵗ ∘ᵗ
      ⟨⟩-≤ (m≤n+m∸n (suc τ) τ') ∘ᵗ
      μ ∘ᵗ
      ⟨ τ' ⟩ᶠ
      (env-⟨⟩-ᶜ (suc τ ∸ τ')
       (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
        (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (ρ ∘ʳ ρ') = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p wk-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ .0 ⟩} (suc τ) p ⟨⟩-η-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p ⟨⟩-η⁻¹-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ .(τ' + τ'') ⟩} (suc τ) p (⟨⟩-μ-ren {τ = τ'} {τ' = τ''}) = {!!}
env-⟨⟩-ᶜ-nat {.(_ ⟨ _ ⟩) ⟨ τ' ⟩} (suc τ) p ⟨⟩-μ⁻¹-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (⟨⟩-≤-ren x) = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (cong-⟨⟩-ren ρ) = {!!}
-}
