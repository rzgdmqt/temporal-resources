----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-naturality (Mod : Model) where


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
  env-⟨⟩-ᶜ-nat : ∀ {Γ Γ'}
               → (τ : Time)
               → (p : τ ≤ ctx-time Γ)
               → (ρ : Ren Γ Γ')
               →    env-⟨⟩-ᶜ {Γ} τ p
                 ∘ᵗ ⟦ ρ ⟧ʳ
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
  ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ (cong (λ p → env-⟨⟩-ᶜ {Γ'} (suc τ) p) (≤-irrelevant _ _))) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵗ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p id-ren with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-identityʳ _ ⟩
       μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (∘ᵗ-identityˡ _)) ⟩
       (   idᵗ
        ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ})
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       idᵗ
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
       ⟨ suc τ ⟩ᶠ idᵗ
    ∘ᵗ μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q =
  begin
         (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
          ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
          ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                       (≤-trans (∸-monoˡ-≤ τ' p)
                        (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
      ∘ᵗ idᵗ
    ≡⟨ ∘ᵗ-identityʳ _ ⟩
         ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' p)
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-cong ⟨ τ' ⟩ᶠ (≡-≡ᵗ (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _))))) ⟩
         ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
         idᵗ
      ∘ᵗ ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
         ⟨ suc τ ⟩ᶠ idᵗ
      ∘ᵗ ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (ρ ∘ʳ ρ') = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p wk-ren with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉ}
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵗ fstᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
       idᵗ
    ∘ᵗ (   μ⁻¹ {⟦ Γ ⟧ᵉ}
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
       ⟨ suc τ ⟩ᶠ idᵗ
    ∘ᵗ (   μ⁻¹ {⟦ Γ ⟧ᵉ}
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵗ fstᵗ
  ∎
... | no ¬q =
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p)
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-cong ⟨ τ' ⟩ᶠ
      (≡-≡ᵗ (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _)))))) ⟩
       (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
        ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵗ fstᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
       idᵗ
    ∘ᵗ (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
        ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
       ⟨ suc τ ⟩ᶠ idᵗ
    ∘ᵗ (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
        ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵗ fstᵗ
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ .0 ⟩} (suc τ) p ⟨⟩-η-ren = 
  begin
       (   ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
        ∘ᵗ μ {⟦ Γ -ᶜ suc τ ⟧ᵉ}
        ∘ᵗ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ)
                    (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))))
    ∘ᵗ η {⟦ Γ ⟧ᵉ}
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
    ∘ᵗ μ {⟦ Γ -ᶜ suc τ ⟧ᵉ}
    ∘ᵗ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ)
                (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0))))
    ∘ᵗ η {⟦ Γ ⟧ᵉ}
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (⟨⟩-η-nat _)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
    ∘ᵗ μ {⟦ Γ -ᶜ suc τ ⟧ᵉ}
    ∘ᵗ η {⟨ suc τ  ⟩ᵒ ⟦ Γ -ᶜ suc τ ⟧ᵉ}
    ∘ᵗ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-trans (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) (∘ᵗ-congˡ ⟨⟩-μ∘η≡id)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
    ∘ᵗ idᵗ
    ∘ᵗ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵗ-congˡ ⟨⟩-≤-refl ⟩
       idᵗ
    ∘ᵗ idᵗ
    ∘ᵗ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵗ-identityˡ _ ⟩
       idᵗ
    ∘ᵗ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ (cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _))) ⟩
       idᵗ
    ∘ᵗ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans p (≤-reflexive (+-identityʳ (ctx-time Γ))))
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
       ⟨ suc τ ⟩ᶠ idᵗ
    ∘ᵗ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans p (≤-reflexive (+-identityʳ (ctx-time Γ))))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p ⟨⟩-η⁻¹-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ .(τ' + τ'') ⟩} (suc τ) p (⟨⟩-μ-ren {τ = τ'} {τ' = τ''}) = {!!}
env-⟨⟩-ᶜ-nat {.(_ ⟨ _ ⟩) ⟨ τ' ⟩} (suc τ) p ⟨⟩-μ⁻¹-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (⟨⟩-≤-ren x) = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (cong-⟨⟩-ren ρ) = {!!}

-}
