-------------------------------------------------------
-- Naturality of the minus operation on environments --
-------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-ren-naturality (Mod : Model) where

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Semantics.Renamings.Properties.-ᶜ-wk-ren-decompose Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

postulate
  env-⟨⟩-ᶜ-ren-nat : ∀ {Γ Γ' A}
                   → (τ : Time)
                   → (p : τ ≤ ctx-time Γ)
                   → (ρ : Ren Γ Γ')
                   →    env-⟨⟩-ᶜ {Γ} τ p 
                     ∘ᵐ ⟦ ρ ⟧ʳ {A}
                   ≡    ⟨ τ ⟩ᶠ ⟦ ρ -ʳ τ ⟧ʳ
                     ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ))

{-
env-⟨⟩-ᶜ-ren-nat zero p ρ = 
  begin
    η ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ sym (⟨⟩-η-nat _) ⟩
    ⟨ 0 ⟩ᶠ ⟦ ρ ⟧ʳ ∘ᵐ η
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ∷ A} {.(Γ ∷ A)} (suc τ) p id-ren = 
  begin
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _)) ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p ≤-refl)
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p ≤-refl)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p ≤-refl)
    ∘ᵐ fstᵐ
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ∷ A} {Γ'} (suc τ) p (_∘ʳ_ {Γ' = Γ''} ρ ρ') = 
  begin
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟦ ρ' ⟧ʳ
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ trans
      (∘ᵐ-assoc _ _ _)
      (trans
        (sym (∘ᵐ-assoc _ _ _))
        (sym (∘ᵐ-assoc _ _ _))) ⟩
       (   (env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
        ∘ᵐ ⟦ ρ' ⟧ʳ)
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (env-⟨⟩-ᶜ-ren-nat (suc τ) p ρ') ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
        ∘ᵐ env-⟨⟩-ᶜ {Γ''} (suc τ) (≤-trans p (ren-≤-ctx-time ρ')))
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ''} (suc τ) (≤-trans p (ren-≤-ctx-time ρ'))
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (env-⟨⟩-ᶜ-ren-nat (suc τ) (≤-trans p (ren-≤-ctx-time ρ')) ρ) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans (≤-trans p (ren-≤-ctx-time ρ')) (ren-≤-ctx-time ρ))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong (env-⟨⟩-ᶜ {Γ'} (suc τ)) (≤-irrelevant _ _))) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ)))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
        ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ  _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (⟦ ρ' -ʳ suc τ ⟧ʳ ∘ᵐ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ)))
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ∷ A} {.(Γ ∷ A ∷ _)} (suc τ) p wk-ren = 
  begin
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _))) ⟩
       (   env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p ≤-refl)
        ∘ᵐ fstᵐ)
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ (   env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p ≤-refl)
        ∘ᵐ fstᵐ)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ (   env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p ≤-refl)
        ∘ᵐ fstᵐ)
    ∘ᵐ fstᵐ
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ∷ A} {.Γ} (suc τ) p (var-ren x) =
  begin
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ ⟧ᵉᶠ terminalᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ ⟧ᵉᶠ terminalᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    env-⟨⟩-ᶜ {Γ} (suc τ) p
  ≡⟨ cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _) ⟩
    env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p (≤-reflexive refl))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p (≤-reflexive refl))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans p (≤-reflexive refl))
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ∷ A} {.((Γ ∷ A) ⟨ 0 ⟩)} (suc τ) p ⟨⟩-η⁻¹-ren =
  {!!}
  {-
  begin
       env-⟨⟩-ᶜ {Γ ∷ A} (suc τ) p
    ∘ᵐ η⁻¹
  ≡⟨⟩
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-η⁻¹-nat _) ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ fstᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ η⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _) ⟩
       (   η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ) p))
    ∘ᵐ ⟨ 0 ⟩ᶠ fstᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ) p)
    ∘ᵐ ⟨ 0 ⟩ᶠ fstᵐ
  ≡⟨ ∘ᵐ-congˡ
      (begin
        η⁻¹
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
           idᵐ
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id) ⟩
           (μ ∘ᵐ η)
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           μ
        ∘ᵐ η
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congʳ ⟨⟩-η∘η⁻¹≡id ⟩
           μ
        ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        μ
      ∎) ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ) p)
    ∘ᵐ ⟨ 0 ⟩ᶠ fstᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _)) ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   env-⟨⟩-ᶜ {Γ} (suc τ) p
               ∘ᵐ fstᵐ)
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ 0 ⟩ᶠ (∘ᵐ-congˡ (cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _)))) ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans
                                         (∸-monoˡ-≤ 0 (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))))
                                         (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
               ∘ᵐ fstᵐ)
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans
                                         (∸-monoˡ-≤ 0 (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))))
                                         (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
               ∘ᵐ fstᵐ)
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-≤-refl) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   env-⟨⟩-ᶜ {Γ} (suc τ) (≤-trans
                                         (∸-monoˡ-≤ 0 (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))))
                                         (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
               ∘ᵐ fstᵐ)
  ≡⟨⟩
    env-⟨⟩-ᶜ {(Γ ∷ A) ⟨ 0 ⟩} (suc τ) (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ)))))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {(Γ ∷ A) ⟨ 0 ⟩} (suc τ) (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ)))))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {(Γ ∷ A) ⟨ 0 ⟩} (suc τ) (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ)))))
  ∎
  -}
env-⟨⟩-ᶜ-ren-nat {Γ ∷ A} {.(_ ∷ A)} (suc τ) p (cong-∷-ren {Γ' = Γ'} ρ) =
  begin
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ ⟦ ρ ⟧ʳ ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ ⟦ ρ ⟧ʳ ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
       env-⟨⟩-ᶜ {Γ} (suc τ) p
    ∘ᵐ (   ⟦ ρ ⟧ʳ
        ∘ᵐ fstᵐ)
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   env-⟨⟩-ᶜ {Γ} (suc τ) p
        ∘ᵐ ⟦ ρ ⟧ʳ)
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (env-⟨⟩-ᶜ-ren-nat (suc τ) p ρ) ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
        ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ)))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ))
    ∘ᵐ fstᵐ
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ τ' ⟩} {A = A} (suc τ) p id-ren with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} {suc τ} {τ' ∸ suc τ}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
       μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} {suc τ} {τ' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _)) ⟩
       (   idᵐ
        ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} {suc τ} {τ' ∸ suc τ})
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       idᵐ
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} {suc τ} {τ' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} {suc τ} {τ' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q =
  {!!}
  {-
  begin
         (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
          ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
          ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                       (≤-trans (∸-monoˡ-≤ τ' p)
                        (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
      ∘ᵐ idᵐ
    ≡⟨ ∘ᵐ-identityʳ _ ⟩
         ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' p)
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _)))) ⟩
         ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
         idᵐ
      ∘ᵐ ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
         ⟨ suc τ ⟩ᶠ idᵐ
      ∘ᵐ ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎
  -}
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ τ' ⟩} (suc τ) p (_∘ʳ_ {Γ' = Γ'} {Γ'' = Γ''} ρ ρ') =
  {!!}
  {-
  begin
       env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} (suc τ) p
    ∘ᵐ ⟦ ρ ∘ʳ ρ' ⟧ʳ
  ≡⟨⟩
       env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} (suc τ) p
    ∘ᵐ ⟦ ρ' ⟧ʳ
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} (suc τ) p
        ∘ᵐ ⟦ ρ' ⟧ʳ)
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (env-⟨⟩-ᶜ-ren-nat (suc τ) p ρ') ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
         ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ')))
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ'))
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (env-⟨⟩-ᶜ-ren-nat (suc τ) (≤-trans p (ren-≤-ctx-time ρ')) ρ) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ''} (suc τ) (≤-trans (≤-trans p (ren-≤-ctx-time ρ')) (ren-≤-ctx-time ρ))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
        ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ {Γ''} (suc τ) (≤-trans (≤-trans p (ren-≤-ctx-time ρ')) (ren-≤-ctx-time ρ))
  ≡⟨ ∘ᵐ-congʳ (cong (env-⟨⟩-ᶜ {Γ''} (suc τ)) (≤-irrelevant _ _)) ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ ρ' -ʳ suc τ ⟧ʳ
        ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ {Γ''} (suc τ) (≤-trans p (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (   ⟦ ρ' -ʳ suc τ ⟧ʳ
                   ∘ᵐ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ  {Γ''} (suc τ) (≤-trans p (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ)))
  ≡⟨⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ∘ʳ ρ' -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ  {Γ''} (suc τ) (≤-trans p (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ)))
  ∎
  -}
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ τ' ⟩} {A = A} (suc τ) p wk-ren with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉᵒ A}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ (   μ⁻¹ {⟦ Γ ⟧ᵉᵒ A}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ (   μ⁻¹ {⟦ Γ ⟧ᵉᵒ A}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ fstᵐ
  ∎
... | no ¬q =
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p)
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
      (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _))))) ⟩
       (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ .0 ⟩} {A = A} (suc τ) p ⟨⟩-η-ren =
  {!!}
  {-
  begin
       (   ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A} ≤-refl
        ∘ᵐ μ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A}
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ)
                    (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))))
    ∘ᵐ η {⟦ Γ ⟧ᵉᵒ A}
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A} ≤-refl
    ∘ᵐ μ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A}
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ)
                (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0))))
    ∘ᵐ η {⟦ Γ ⟧ᵉᵒ A}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-η-nat _)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A} ≤-refl
    ∘ᵐ μ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A}
    ∘ᵐ η {⟨ suc τ  ⟩ᵒ (⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A)}
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-μ∘η≡id)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉᵒ A} ≤-refl
    ∘ᵐ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-congˡ ⟨⟩-≤-refl ⟩
       idᵐ
    ∘ᵐ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-congʳ (cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _)) ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans p (≤-reflexive (+-identityʳ (ctx-time Γ))))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans p (≤-reflexive (+-identityʳ (ctx-time Γ))))
  ∎
  -}
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ τ' ⟩} (suc τ) p ⟨⟩-η⁻¹-ren with suc τ ≤? τ'
... | yes q =
  {!!}
  {-
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-η⁻¹-nat _) ⟩
       μ⁻¹
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   μ⁻¹
        ∘ᵐ η⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _) ⟩
       (   η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (
      begin
        η⁻¹
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
           idᵐ
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id) ⟩
           (   μ
            ∘ᵐ η)
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           μ
        ∘ᵐ η
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congʳ ⟨⟩-η∘η⁻¹≡id ⟩
           μ
        ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        μ
      ∎)) ⟩
       (   μ
        ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-≤-refl) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ∎
  -}
... | no ¬q =
  {!!}
  {-
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ η⁻¹
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-η⁻¹-nat _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ idᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ (μ ∘ᵐ η)
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
      (trans
        (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ μ
    ∘ᵐ (   η
        ∘ᵐ η⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-η∘η⁻¹≡id))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ μ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   μ
        ∘ᵐ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-μ∘μ≡μ∘Tμ) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   ⟨⟩-≤ (≤-reflexive (+-assoc 0 τ' _))
        ∘ᵐ μ
        ∘ᵐ ⟨ 0 ⟩ᶠ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   ⟨⟩-≤ ≤-refl
        ∘ᵐ μ
        ∘ᵐ ⟨ 0 ⟩ᶠ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-congˡ ⟨⟩-≤-refl)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   idᵐ
        ∘ᵐ μ
        ∘ᵐ ⟨ 0 ⟩ᶠ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-identityˡ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ (   μ
        ∘ᵐ ⟨ 0 ⟩ᶠ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) (sym (∘ᵐ-assoc _ _ _)) ⟩
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
       (   ⟨⟩-≤ (+-monoʳ-≤ 0 (m≤n+m∸n (suc τ) τ'))
        ∘ᵐ μ)
    ∘ᵐ ⟨ 0 ⟩ᶠ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-μ-≤₂ _) ⟩
       (   μ
        ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (m≤n+m∸n (suc τ) τ')))
    ∘ᵐ ⟨ 0 ⟩ᶠ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (m≤n+m∸n (suc τ) τ'))
    ∘ᵐ ⟨ 0 ⟩ᶠ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ 0 ⟩ᶠ (cong ⟨ τ' ⟩ᶠ (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _)))))) ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (m≤n+m∸n (suc τ) τ'))
    ∘ᵐ ⟨ 0 ⟩ᶠ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                         (≤-trans
                           (∸-monoˡ-≤ τ'
                             (≤-trans
                               (∸-mono {u = 0}
                                 (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                               (≤-reflexive (+-identityʳ (ctx-time Γ + τ')))))
                           (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ
      (sym
        (trans
          (⟨⟩-∘ᵐ _ _)
          (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))) ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
               ∘ᵐ μ
               ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                            (≤-trans
                              (∸-monoˡ-≤ τ'
                                (≤-trans
                                  (∸-mono {u = 0}
                                    (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                                  (≤-reflexive (+-identityʳ (ctx-time Γ + τ')))))
                              (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
               ∘ᵐ μ
               ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                            (≤-trans
                              (∸-monoˡ-≤ τ'
                                (≤-trans
                                  (∸-mono {u = 0}
                                    (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                                  (≤-reflexive (+-identityʳ (ctx-time Γ + τ')))))
                              (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
               ∘ᵐ μ
               ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                            (≤-trans
                              (∸-monoˡ-≤ τ'
                                (≤-trans
                                  (∸-mono {u = 0}
                                    (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                                  (≤-reflexive (+-identityʳ (ctx-time Γ + τ')))))
                              (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
               ∘ᵐ μ
               ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                            (≤-trans
                              (∸-monoˡ-≤ τ'
                                (≤-trans
                                  (∸-mono {u = 0}
                                    (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                                  (≤-reflexive (+-identityʳ (ctx-time Γ + τ')))))
                              (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-≤-refl)) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
               ∘ᵐ μ
               ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                            (≤-trans
                              (∸-monoˡ-≤ τ'
                                (≤-trans
                                  (∸-mono {u = 0}
                                    (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                                  (≤-reflexive (+-identityʳ (ctx-time Γ + τ')))))
                              (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ 0 ⟩ᶠ
      (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
        (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _)))))))) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
               ∘ᵐ μ
               ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                            (≤-trans
                              (∸-monoˡ-≤ τ'
                                (≤-trans
                                  (∸-mono {u = 0}
                                    (≤-trans p (≤-reflexive (sym (+-identityʳ (ctx-time Γ + τ'))))) z≤n)
                                  (≤-reflexive _)))
                              (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
  ∎
  -}
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ .(τ' + τ'') ⟩} {A = A} (suc τ) p (⟨⟩-μ-ren {τ = τ'} {τ' = τ''}) with suc τ ≤? τ' + τ'' | suc τ ≤? τ''
... | yes q | yes r =
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ''))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ''))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       μ⁻¹
    ∘ᵐ (   ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ'')))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (
      trans
        (⟨⟩-≤-trans _ _)
        (sym (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-≤-trans _ _)))
          (trans (∘ᵐ-congʳ (⟨⟩-≤-trans _ _))
            (trans (⟨⟩-≤-trans _ _) (cong ⟨⟩-≤ (≤-irrelevant _ _)))))))) ⟩
       μ⁻¹
    ∘ᵐ (   ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (≤-reflexive (+-∸-assoc τ' r)))
        ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc (suc τ) (τ'' ∸ suc τ) τ')))
        ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ τ' (≤-reflexive (m+[n∸m]≡n r))))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (≤-reflexive (+-∸-assoc τ' r)))
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc (suc τ) (τ'' ∸ suc τ) τ')))
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ τ' (≤-reflexive (m+[n∸m]≡n r)))
    ∘ᵐ μ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩-μ⁻¹-≤₂ _)) (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-∸-assoc τ' r)))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc (suc τ) (τ'' ∸ suc τ) τ')))
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ τ' (≤-reflexive (m+[n∸m]≡n r)))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩-μ⁻¹-≤₂ _)) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-∸-assoc τ' r)))
    ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc (suc τ) (τ'' ∸ suc τ) τ')))
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ τ' (≤-reflexive (m+[n∸m]≡n r)))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-μ-≤₁ _)))) ⟩
       ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-∸-assoc τ' r)))
    ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-assoc (suc τ) (τ'' ∸ suc τ) τ')))
    ∘ᵐ μ
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n r))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _))
      (trans (∘ᵐ-congˡ ⟨⟩-Tμ∘μ⁻¹≡μ⁻¹∘μ) (trans (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩ 
       ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-∸-assoc τ' r)))
    ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
    ∘ᵐ ⟨ suc τ ⟩ᶠ μ
    ∘ᵐ μ⁻¹ {⟨ τ' ⟩ᵒ (⟦ Γ ⟧ᵉᵒ A)} {suc τ} {τ'' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n r))
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
       (   ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-∸-assoc τ' r)))
        ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ' (τ'' ∸ suc τ))))
        ∘ᵐ ⟨ suc τ ⟩ᶠ μ)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n r))
  ≡⟨ ∘ᵐ-congˡ (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))) ⟩
       ⟨ suc τ ⟩ᶠ (   ⟨⟩-≤ (≤-reflexive (+-∸-assoc τ' r))
                   ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' (τ'' ∸ suc τ)))
                   ∘ᵐ μ)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n r))
  ∎
... | yes q | no ¬r = {!!}
... | no ¬q | yes r =
  ⊥-elim (n≤k⇒¬n≤m+k-contradiction r ¬q)
... | no ¬q | no ¬r = {!!}
env-⟨⟩-ᶜ-ren-nat {.(_ ⟨ _ ⟩) ⟨ τ' ⟩} (suc τ) p ⟨⟩-μ⁻¹-ren = {!!}
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ τ' ⟩} (suc τ) p (⟨⟩-≤-ren {τ' = τ''} q) with suc τ ≤? τ' | suc τ ≤? τ''
... | yes r | yes s =
  {!!}
  {-
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n r)))
    ∘ᵐ ⟨⟩-≤ q
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n r))
    ∘ᵐ ⟨⟩-≤ q
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-≤-trans _ _) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-trans (≤-reflexive (m+[n∸m]≡n r)) q)
  ≡⟨ ∘ᵐ-congʳ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-trans (+-monoʳ-≤ (suc τ) (∸-monoˡ-≤ (suc τ) q)) (≤-reflexive (m+[n∸m]≡n s)))
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-≤-trans _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (∸-monoˡ-≤ (suc τ) q))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) (∸-monoˡ-≤ (suc τ) q)))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-μ⁻¹-≤₂ _) ⟩
       (   ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (∸-monoˡ-≤ (suc τ) q))
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ (⟨⟩-≤ (∸-monoˡ-≤ (suc τ) q))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ∎
  -}
... | yes r | no ¬s =
  ⊥-elim (¬s (≤-trans r q))
... | no ¬r | yes s =
  {!!}
  {-
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p)
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ ⟨⟩-≤ q
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                 (≤-trans (∸-monoˡ-≤ τ' p)
                  (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ ⟨⟩-≤ q
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-≤-nat _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨⟩-≤ q
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-μ-≤₁ _))) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ ⟨⟩-≤ (+-monoˡ-≤ (suc τ ∸ τ') q)
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
      (trans (⟨⟩-≤-trans _ _)
        (sym (trans (∘ᵐ-congʳ (⟨⟩-≤-trans _ _))
          (trans (⟨⟩-≤-trans _ _) (cong ⟨⟩-≤ (≤-irrelevant _ _))))))) ⟩
       (   ⟨⟩-≤ s
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ τ'' z≤n))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ τ'' z≤n)
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ (   ⟨⟩-≤ (+-monoʳ-≤ τ'' z≤n)
        ∘ᵐ μ) 
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-μ-≤₂ _))) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ (   μ
        ∘ᵐ ⟨ τ'' ⟩ᶠ (⟨⟩-≤ z≤n))
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ'' ⟩ᶠ (⟨⟩-≤ z≤n)
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ s
    ∘ᵐ (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵐ μ)
    ∘ᵐ ⟨ τ'' ⟩ᶠ (⟨⟩-≤ z≤n)
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ
      (trans (∘ᵐ-congˡ (sym ⟨⟩-Tη⁻¹∘μ⁻¹≡id))
        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ ⟨⟩-μ⁻¹∘μ≡id) (∘ᵐ-identityʳ _))))) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨ τ'' ⟩ᶠ η⁻¹
    ∘ᵐ ⟨ τ'' ⟩ᶠ (⟨⟩-≤ z≤n)
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                  (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (sym (trans (⟨⟩-∘ᵐ _ _) (trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨ τ'' ⟩ᶠ (   (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
                 ∘ᵐ env-⟨⟩-ᶜ (suc τ ∸ τ')
                      (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ τ'' ⟩ᶠ (sym (⟦-ᶜ-wk-ren⟧ʳ≡ε∘env-⟨⟩-ᶜ _))) ⟩
       ⟨⟩-≤ s
    ∘ᵐ ⟨ τ'' ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤ (≤-trans
              (≤-reflexive (sym (+-identityʳ _)))
              (≤-trans (+-monoʳ-≤ (suc τ) z≤n) (≤-reflexive (m+[n∸m]≡n s))))
    ∘ᵐ ⟨ τ'' ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)) ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵐ ⟨⟩-≤ (≤-trans (+-monoʳ-≤ (suc τ) z≤n) (≤-reflexive (m+[n∸m]≡n s))))
    ∘ᵐ ⟨ τ'' ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ ⟨⟩-≤ (≤-trans (+-monoʳ-≤ (suc τ) z≤n) (≤-reflexive (m+[n∸m]≡n s)))
    ∘ᵐ ⟨ τ'' ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ ⟨ suc τ + 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (≤-trans (+-monoʳ-≤ (suc τ) z≤n) (≤-reflexive (m+[n∸m]≡n s)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-≤-trans _ _))) ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ _)))
    ∘ᵐ ⟨ suc τ + 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-Tη⁻¹∘μ⁻¹≡id) ⟩
       (   ⟨ suc τ ⟩ᶠ η⁻¹
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨ suc τ + 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨ suc τ + 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ (   μ⁻¹
        ∘ᵐ ⟨ suc τ + 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ)
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-μ⁻¹-nat _))) ⟩
       ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ (   ⟨ suc τ ⟩ᶠ (⟨ 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ)
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
       ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨ 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨ suc τ ⟩ᶠ η⁻¹
        ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨ 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (   η⁻¹
                   ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congˡ (cong ⟨ suc τ ⟩ᶠ (sym (⟨⟩-η⁻¹-nat _))) ⟩
       ⟨ suc τ ⟩ᶠ (   ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
                   ∘ᵐ η⁻¹)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _) ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
        ∘ᵐ ⟨ suc τ ⟩ᶠ η⁻¹)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (+-monoʳ-≤ (suc τ) z≤n))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-μ⁻¹-≤₂ _))) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ (   ⟨ suc τ ⟩ᶠ (⟨⟩-≤ z≤n)
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨ suc τ ⟩ᶠ η⁻¹
    ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨⟩-≤ z≤n)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
       (   ⟨ suc τ ⟩ᶠ ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
        ∘ᵐ ⟨ suc τ ⟩ᶠ η⁻¹
        ∘ᵐ ⟨ suc τ ⟩ᶠ (⟨⟩-≤ z≤n))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ≡⟨ ∘ᵐ-congˡ (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))) ⟩
       ⟨ suc τ ⟩ᶠ (   ⟦ -ᶜ-wk-ren (suc τ ∸ τ') ⟧ʳ
                   ∘ᵐ η⁻¹
                   ∘ᵐ ⟨⟩-≤ z≤n)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n s))
  ∎
  -}
... | no ¬r | no ¬s =
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ ⟨⟩-≤ q
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ ⟨⟩-≤ q
  ≡⟨ {!!} ⟩
       ⟨ suc τ ⟩ᶠ (   ⟦ eq-ren (cong (_-ᶜ_ Γ) (sym (m+n∸m≡n (suc τ ∸ τ'') (suc τ ∸ τ')))) ⟧ʳ
                   ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ Γ) (+-∸-assoc (suc τ ∸ τ'') (∸-monoʳ-≤ (suc τ) q))) ⟧ʳ
                   ∘ᵐ ⟦ eq-ren (++ᶜ-ᶜ-+ {Γ} {suc τ ∸ τ''}) ⟧ʳ
                   ∘ᵐ ⟦ -ᶜ-wk-ren (suc τ ∸ τ' ∸ (suc τ ∸ τ'')) ⟧ʳ)
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ'')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ'' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ'') (≤-trans (∸-monoˡ-≤ τ''
                  (≤-trans p (+-mono-≤ (≤-reflexive refl) q))) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ''))))
  ∎
env-⟨⟩-ᶜ-ren-nat {Γ ⟨ τ' ⟩} (suc τ) p (cong-⟨⟩-ren {Γ' = Γ'} ρ) with suc τ ≤? τ'
... | yes q =
  {!!}
  {-
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨ suc τ + (τ' ∸ suc τ) ⟩ᶠ ⟦ ρ ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _))
      (trans (∘ᵐ-congˡ (sym (⟨⟩-μ⁻¹-nat _))) (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ ⟦ ρ ⟧ʳ)
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ∎
  -}
... | no ¬q =
  {!!}
  {-
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))
                ∘ᵐ ⟦ ρ ⟧ʳ)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ-ren-nat (suc τ ∸ τ') _ ρ))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨ suc τ ∸ τ' ⟩ᶠ ⟦ ρ -ʳ (suc τ ∸ τ') ⟧ʳ
                ∘ᵐ env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans
                     (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ ⟦ ρ -ʳ (suc τ ∸ τ') ⟧ʳ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans
                 (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))) (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _))))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ ⟦ ρ -ʳ (suc τ ∸ τ') ⟧ʳ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ'
                 (≤-trans p (+-mono-≤ (ren-≤-ctx-time ρ) (≤-reflexive refl)))) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ'))))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-μ-nat _))) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ ⟦ ρ -ʳ (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ'
                 (≤-trans p (+-mono-≤ (ren-≤-ctx-time ρ) (≤-reflexive refl)))) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ'))))
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-≤-nat _ _))) (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ (suc τ ∸ τ') ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ') (≤-trans (∸-monoˡ-≤ τ'
                 (≤-trans p (+-mono-≤ (ren-≤-ctx-time ρ) (≤-reflexive refl)))) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ'))))
  ∎
  -}

-}
