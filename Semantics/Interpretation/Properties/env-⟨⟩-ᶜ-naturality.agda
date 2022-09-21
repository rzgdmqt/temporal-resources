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

env-⟨⟩-ᶜ-nat : ∀ {Γ A B}
             → (τ : Time)
             → (p : τ ≤ ctx-time Γ)
             → (f : A →ᵐ B)
             →    env-⟨⟩-ᶜ {Γ} τ p 
               ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
             ≡    ⟨ τ ⟩ᶠ (⟦ Γ -ᶜ τ ⟧ᵉᶠ f)
               ∘ᵐ env-⟨⟩-ᶜ {Γ} τ p 

env-⟨⟩-ᶜ-nat {Γ} {A} {B} zero p f = 
  begin
    η ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
  ≡⟨ sym (⟨⟩-η-nat _) ⟩
    ⟨ 0 ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f) ∘ᵐ η
  ∎
env-⟨⟩-ᶜ-nat {Γ ∷ _} {A} {B} (suc τ) p f = 
  begin
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ ⟦ Γ ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ ⟦ Γ ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ ⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (env-⟨⟩-ᶜ-nat {Γ} (suc τ) p f) ⟩
       (   ⟨ suc τ ⟩ᶠ (⟦ Γ -ᶜ suc τ ⟧ᵉᶠ f)
        ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) p)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ (⟦ Γ -ᶜ suc τ ⟧ᵉᶠ f)
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} {A} {B} (suc τ) p f with suc τ ≤? τ'
... | yes q = 
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨ suc (τ + (τ' ∸ suc τ)) ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   μ⁻¹
        ∘ᵐ ⟨ suc (τ + (τ' ∸ suc τ)) ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-μ⁻¹-nat _)) ⟩
       (   ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q = 
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                 (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))
                ∘ᵐ ⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
      (env-⟨⟩-ᶜ-nat (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) f))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨ suc τ ∸ τ' ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f)
                ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) )
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f))
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) )
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f)))
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) )
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-μ-nat _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f)
        ∘ᵐ μ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) )
  ≡⟨ trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) (sym (∘ᵐ-assoc _ _ _)) ⟩
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) )
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-nat _ _)) ⟩
       (   ⟨ suc τ ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f)
        ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ'))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) )
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ (⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᶠ f)
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                 (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎
