{-

--------------------------------------------------------
-- Naturality of etracting the time of an environment --
--------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-ctx-time-⟨⟩-naturality (Mod : Model) where

open import Data.Product

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

env-ctx-time-⟨⟩-nat : ∀ {Γ Γ'}
                    → (ρ : Ren Γ Γ')
                    →    env-ctx-time-⟨⟩ Γ
                      ∘ᵐ ⟦ ρ ⟧ʳ 
                    ≡    ⟨⟩-≤ (ren-≤-ctx-time ρ)
                      ∘ᵐ env-ctx-time-⟨⟩ Γ'
                      
env-ctx-time-⟨⟩-nat {Γ} {.Γ} id-ren =
  begin
    env-ctx-time-⟨⟩ Γ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    env-ctx-time-⟨⟩ Γ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ env-ctx-time-⟨⟩ Γ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-≤-refl) ⟩
    ⟨⟩-≤ ≤-refl ∘ᵐ env-ctx-time-⟨⟩ Γ
  ∎
env-ctx-time-⟨⟩-nat {Γ} {Γ'} (_∘ʳ_ {Γ' = Γ''} ρ ρ') =
  begin
       env-ctx-time-⟨⟩ Γ
    ∘ᵐ ⟦ ρ' ⟧ʳ
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   env-ctx-time-⟨⟩ Γ
        ∘ᵐ ⟦ ρ' ⟧ʳ)
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (env-ctx-time-⟨⟩-nat ρ') ⟩
       (   ⟨⟩-≤ (ren-≤-ctx-time ρ')
        ∘ᵐ env-ctx-time-⟨⟩ Γ'')
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨⟩-≤ (ren-≤-ctx-time ρ')
    ∘ᵐ env-ctx-time-⟨⟩ Γ''
    ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (env-ctx-time-⟨⟩-nat ρ) ⟩
       ⟨⟩-≤ (ren-≤-ctx-time ρ')
    ∘ᵐ ⟨⟩-≤  (ren-≤-ctx-time ρ)
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨⟩-≤ (ren-≤-ctx-time ρ')
        ∘ᵐ ⟨⟩-≤  (ren-≤-ctx-time ρ))
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-≤-trans _ _) ⟩
       ⟨⟩-≤ (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ))
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ∎
env-ctx-time-⟨⟩-nat {Γ} {.(Γ ∷ _)} wk-ren = 
  begin
    env-ctx-time-⟨⟩ Γ ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ env-ctx-time-⟨⟩ Γ ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-≤-refl) ⟩
    ⟨⟩-≤ ≤-refl ∘ᵐ env-ctx-time-⟨⟩ Γ ∘ᵐ fstᵐ
  ∎
env-ctx-time-⟨⟩-nat {.(Γ' ∷ _)} {Γ'} (var-ren x) =
  begin
       (   env-ctx-time-⟨⟩ Γ'
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ idᵐ , var-in-env x ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       env-ctx-time-⟨⟩ Γ'
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ idᵐ , var-in-env x ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
       env-ctx-time-⟨⟩ Γ'
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    env-ctx-time-⟨⟩ Γ'
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-≤-refl) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ∎
env-ctx-time-⟨⟩-nat {.(Γ' ⟨ 0 ⟩)} {Γ'} ⟨⟩-η-ren =
  begin
       (   ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
        ∘ᵐ μ 
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ'))
    ∘ᵐ η
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵐ μ 
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-η-nat _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵐ μ 
    ∘ᵐ η
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵐ (   μ 
        ∘ᵐ η)
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-μ∘η≡id) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵐ idᵐ
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-identityʳ (ctx-time Γ')))
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
  ∎
env-ctx-time-⟨⟩-nat {Γ} {.(Γ ⟨ 0 ⟩)} ⟨⟩-η⁻¹-ren =
  begin
       env-ctx-time-⟨⟩ Γ
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-congˡ (
      begin
        env-ctx-time-⟨⟩ Γ
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
           idᵐ
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-refl)) ⟩
           ⟨⟩-≤  ≤-refl
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
           (⟨⟩-≤  (≤-trans
             (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
             (≤-reflexive (+-comm (ctx-time Γ) 0))))
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)) ⟩
           (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
            ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0)))
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ idᵐ
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id))) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ (μ 
            ∘ᵐ η)
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ μ 
        ∘ᵐ η
        ∘ᵐ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-η-nat _)))) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ μ 
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
        ∘ᵐ η
      ∎) ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ μ 
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
        ∘ᵐ η)
    ∘ᵐ η⁻¹
  ≡⟨ sym
      (trans
        (∘ᵐ-assoc _ _ _)
        (trans
          (∘ᵐ-congʳ
            (trans
              (trans
                (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ (trans
                  (∘ᵐ-assoc _ _ _)
                  (trans
                    (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))
                    (sym (∘ᵐ-assoc _ _ _))))))
              (sym (∘ᵐ-assoc _ _ _))))
          (sym (∘ᵐ-assoc _ _ _)))) ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ μ 
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵐ (η ∘ᵐ η⁻¹)
  ≡⟨ ∘ᵐ-congʳ ⟨⟩-η∘η⁻¹≡id ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵐ μ 
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
    ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) 0))
    ∘ᵐ μ 
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ∎
env-ctx-time-⟨⟩-nat {.(_ ⟨ τ + τ' ⟩)} {.((_ ⟨ _ ⟩) ⟨ _ ⟩)} (⟨⟩-μ-ren {Γ} {τ} {τ'}) = 
  begin
       (   ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ) (τ + τ')))
        ∘ᵐ μ
        ∘ᵐ ⟨ τ + τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ τ'))
    ∘ᵐ μ
  ≡⟨ {!!} ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ) τ)))
    ∘ᵐ ⟨ τ' ⟩ᶠ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))))) ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ)))
    ∘ᵐ ⟨ τ' ⟩ᶠ (   μ 
                ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _)))) ⟩
       ⟨⟩-≤  (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))
    ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
                ∘ᵐ μ 
                ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
  ∎
env-ctx-time-⟨⟩-nat {.((_ ⟨ _ ⟩) ⟨ _ ⟩)} {.(_ ⟨ τ + τ' ⟩)} (⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'}) = 
  begin
       (   ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ) τ))
                    ∘ᵐ μ
                    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
  ≡⟨ {!!} ⟩
      ⟨⟩-≤ (≤-reflexive (+-assoc (ctx-time Γ) τ τ')) ∘ᵐ
      ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ) (τ + τ'))) ∘ᵐ
      μ ∘ᵐ ⟨ τ + τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ∎
env-ctx-time-⟨⟩-nat {.(_ ⟨ _ ⟩)} {.(_ ⟨ _ ⟩)}  (⟨⟩-≤-ren {Γ} {τ} {τ'} p) =
  begin
       (   ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵐ μ 
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵐ ⟨⟩-≤ p
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
    ∘ᵐ ⟨⟩-≤ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
        ∘ᵐ ⟨⟩-≤ p
      ≡⟨ ⟨⟩-≤-nat _ _ ⟩
           ⟨⟩-≤ p
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
           idᵐ
        ∘ᵐ ⟨⟩-≤ p
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
           ⟨ τ ⟩ᶠ idᵐ
        ∘ᵐ ⟨⟩-≤ p
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ≡⟨ ∘ᵐ-congˡ (sym (cong ⟨ τ ⟩ᶠ ⟨⟩-≤-refl)) ⟩
           ⟨ τ ⟩ᶠ (⟨⟩-≤  ≤-refl)
        ∘ᵐ ⟨⟩-≤ p
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ∎)) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  ≤-refl)
    ∘ᵐ ⟨⟩-≤ p
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵐ-congʳ
      (trans
        (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))
        (sym (∘ᵐ-assoc _ _ _))) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ (   μ 
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  ≤-refl)
        ∘ᵐ ⟨⟩-≤ p)
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (⟨⟩-μ-≤ p ≤-refl))) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ (   ⟨⟩-≤  (+-mono-≤ p ≤-refl)
        ∘ᵐ μ )
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) (sym (∘ᵐ-assoc _ _ _)) ⟩
       (   ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵐ ⟨⟩-≤  (+-mono-≤ p ≤-refl))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-≤-trans _ _) ⟩
       ⟨⟩-≤  (≤-trans (≤-reflexive (+-comm (ctx-time Γ) τ)) (+-mono-≤ p ≤-refl))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤  (≤-trans (+-monoʳ-≤ (ctx-time Γ) p) (≤-reflexive (+-comm (ctx-time Γ) τ')))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)) ⟩
       (   ⟨⟩-≤  (+-monoʳ-≤ (ctx-time Γ) p)
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ')))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨⟩-≤  (+-monoʳ-≤ (ctx-time Γ) p)
    ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ'))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ∎
env-ctx-time-⟨⟩-nat {.(_ ∷ _)} {.(_ ∷ _)}  (cong-∷-ren {Γ} {Γ'} {B} ρ) =
  begin
       (env-ctx-time-⟨⟩ Γ ∘ᵐ fstᵐ)
    ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       env-ctx-time-⟨⟩ Γ
    ∘ᵐ fstᵐ
    ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
       env-ctx-time-⟨⟩ Γ
    ∘ᵐ ⟦ ρ ⟧ʳ 
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   env-ctx-time-⟨⟩ Γ
        ∘ᵐ ⟦ ρ ⟧ʳ )
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (env-ctx-time-⟨⟩-nat ρ) ⟩
       (   ⟨⟩-≤  (ren-≤-ctx-time ρ)
        ∘ᵐ env-ctx-time-⟨⟩ Γ')
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨⟩-≤  (ren-≤-ctx-time ρ)
    ∘ᵐ env-ctx-time-⟨⟩ Γ'
    ∘ᵐ fstᵐ
  ∎
env-ctx-time-⟨⟩-nat {.(_ ⟨ _ ⟩)} {.(_ ⟨ _ ⟩)}  (cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ) =
  begin
       (   ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵐ μ 
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ ∘ᵐ ⟦ ρ ⟧ʳ)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩-nat ρ))) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ μ 
    ∘ᵐ (⟨ τ ⟩ᶠ (⟨⟩-≤  (ren-≤-ctx-time ρ) ∘ᵐ env-ctx-time-⟨⟩ Γ'))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  (ren-≤-ctx-time ρ))
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ (   μ 
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  (ren-≤-ctx-time ρ)))
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ
      (begin
        μ  ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  (ren-≤-ctx-time ρ))
      ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)) ⟩
        μ  ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  (ren-≤-ctx-time ρ)) ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym ⟨⟩-≤-refl)) ⟩
        μ  ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤  (ren-≤-ctx-time ρ)) ∘ᵐ ⟨⟩-≤ ≤-refl
      ≡⟨ sym (⟨⟩-μ-≤ _ _) ⟩
        ⟨⟩-≤  (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ)) ∘ᵐ μ 
      ∎)) ⟩
       ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵐ (  ⟨⟩-≤  (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ))
       ∘ᵐ μ )
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ sym
      (trans
        (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))) ⟩
       (⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵐ ⟨⟩-≤  (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ)))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-≤-trans _ _) ⟩
       ⟨⟩-≤  (≤-trans (≤-reflexive (+-comm (ctx-time Γ) τ)) (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ)))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤  (≤-trans (+-monoˡ-≤ τ (ren-≤-ctx-time ρ)) (≤-reflexive (+-comm (ctx-time Γ') τ)))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-≤-trans _ _)) ⟩
       (   ⟨⟩-≤  (+-monoˡ-≤ τ (ren-≤-ctx-time ρ))
        ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ') τ)))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨⟩-≤  (+-monoˡ-≤ τ (ren-≤-ctx-time ρ))
    ∘ᵐ ⟨⟩-≤  (≤-reflexive (+-comm (ctx-time Γ') τ))
    ∘ᵐ μ 
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ∎


-}
