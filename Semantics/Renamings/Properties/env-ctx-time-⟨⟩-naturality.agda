module Semantics.Renamings.Properties.env-ctx-time-⟨⟩-naturality where

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

env-ctx-time-⟨⟩-nat : ∀ {Γ Γ' A}
                    → (ρ : Ren Γ Γ')
                    →    env-ctx-time-⟨⟩ Γ
                      ∘ᵗ ⟦ ρ ⟧ʳ {A}
                   ≡ᵗ    ⟨⟩-≤ {A} (ren-≤-ctx-time ρ)
                      ∘ᵗ env-ctx-time-⟨⟩ Γ'
                      
env-ctx-time-⟨⟩-nat {Γ} {.Γ} id-ren =
  begin
    env-ctx-time-⟨⟩ Γ ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-identityʳ _ ⟩
    env-ctx-time-⟨⟩ Γ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
    idᵗ ∘ᵗ env-ctx-time-⟨⟩ Γ
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-≤-refl) ⟩
    ⟨⟩-≤ ≤-refl ∘ᵗ env-ctx-time-⟨⟩ Γ
  ∎
env-ctx-time-⟨⟩-nat {Γ} {Γ'} {A} (_∘ʳ_ {Γ' = Γ''} ρ ρ') =
  {!!}
{-
  begin
       env-ctx-time-⟨⟩ Γ
    ∘ᵗ ⟦ ρ' ⟧ʳ
    ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
       (   env-ctx-time-⟨⟩ Γ
        ∘ᵗ ⟦ ρ' ⟧ʳ)
    ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-congˡ (env-ctx-time-⟨⟩-nat ρ') ⟩
       (   ⟨⟩-≤ (ren-≤-ctx-time ρ')
        ∘ᵗ env-ctx-time-⟨⟩ Γ'')
    ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       ⟨⟩-≤ (ren-≤-ctx-time ρ')
    ∘ᵗ env-ctx-time-⟨⟩ Γ''
    ∘ᵗ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-congʳ (env-ctx-time-⟨⟩-nat ρ) ⟩
       ⟨⟩-≤ (ren-≤-ctx-time ρ')
    ∘ᵗ ⟨⟩-≤ {A} (ren-≤-ctx-time ρ)
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
       (   ⟨⟩-≤ (ren-≤-ctx-time ρ')
        ∘ᵗ ⟨⟩-≤ {A} (ren-≤-ctx-time ρ))
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵗ-congˡ (⟨⟩-≤-trans _ _) ⟩
       ⟨⟩-≤ (≤-trans (ren-≤-ctx-time ρ') (ren-≤-ctx-time ρ))
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ∎
-}
env-ctx-time-⟨⟩-nat {Γ} {.(Γ ∷ _)} wk-ren = 
  begin
    env-ctx-time-⟨⟩ Γ ∘ᵗ fstᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
    idᵗ ∘ᵗ env-ctx-time-⟨⟩ Γ ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-≤-refl) ⟩
    ⟨⟩-≤ ≤-refl ∘ᵗ env-ctx-time-⟨⟩ Γ ∘ᵗ fstᵗ
  ∎
env-ctx-time-⟨⟩-nat {.(Γ' ∷ _)} {Γ'} (var-ren x) =
  {!!}
{-
  begin
    (env-ctx-time-⟨⟩ Γ' ∘ᵗ fstᵗ) ∘ᵗ
      ⟨ idᵗ ,    ε-⟨⟩
              ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
              ∘ᵗ var-in-env x ⟩ᵗ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       env-ctx-time-⟨⟩ Γ'
    ∘ᵗ (   fstᵗ
        ∘ᵗ ⟨ idᵗ ,    ε-⟨⟩
                   ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
                   ∘ᵗ var-in-env x ⟩ᵗ)
  ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _) ⟩
       env-ctx-time-⟨⟩ Γ'
    ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-identityʳ _ ⟩
       env-ctx-time-⟨⟩ Γ'
  ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
    idᵗ ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-≤-refl) ⟩
    ⟨⟩-≤ ≤-refl ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ∎
-}
env-ctx-time-⟨⟩-nat {.(Γ' ⟨ 0 ⟩)} {Γ'} {A} ⟨⟩-η-ren =
  {!!}
{-
  begin
       (   ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ'))
    ∘ᵗ η
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
    ∘ᵗ η
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (⟨⟩-η-nat _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵗ μ {A}
    ∘ᵗ η
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵗ (   μ {A}
        ∘ᵗ η)
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ ⟨⟩-μ∘η≡id) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵗ idᵗ
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-identityˡ _) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm (ctx-time Γ') 0))
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ≡⟨ ∘ᵗ-congˡ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
       ⟨⟩-≤ (≤-reflexive (+-identityʳ (ctx-time Γ')))
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
  ∎
-}
env-ctx-time-⟨⟩-nat {Γ} {.(Γ ⟨ 0 ⟩)} {A} ⟨⟩-η⁻¹-ren =
  {!!}
{-
  begin
       env-ctx-time-⟨⟩ Γ
    ∘ᵗ η⁻¹
  ≡⟨ ∘ᵗ-congˡ (
      begin
        env-ctx-time-⟨⟩ Γ
      ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
           idᵗ
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-refl)) ⟩
           ⟨⟩-≤ {A} ≤-refl
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congˡ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
           (⟨⟩-≤ {A} (≤-trans
             (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
             (≤-reflexive (+-comm (ctx-time Γ) 0))))
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _)) ⟩
           (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
            ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0)))
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityˡ _))) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ idᵗ
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-μ∘η≡id))) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ (μ {A}
            ∘ᵗ η)
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ μ {A}
        ∘ᵗ η
        ∘ᵗ env-ctx-time-⟨⟩ Γ
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-η-nat _)))) ⟩
           ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
        ∘ᵗ η {⟦ Γ ⟧ᵉᵒ A}
      ∎) ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
        ∘ᵗ η {⟦ Γ ⟧ᵉᵒ A})
    ∘ᵗ η⁻¹ {⟦ Γ ⟧ᵉᵒ A}
  ≡⟨ ≡ᵗ-sym
      (≡ᵗ-trans
        (∘ᵗ-assoc _ _ _)
        (≡ᵗ-trans
          (∘ᵗ-congʳ
            (≡ᵗ-trans
              (≡ᵗ-trans
                (∘ᵗ-assoc _ _ _)
                (∘ᵗ-congʳ (≡ᵗ-trans
                  (∘ᵗ-assoc _ _ _)
                  (≡ᵗ-trans
                    (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))
                    (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))))
              (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))
          (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))) ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵗ (η ∘ᵗ η⁻¹ {⟦ Γ ⟧ᵉᵒ A})
  ≡⟨ ∘ᵗ-congʳ ⟨⟩-η∘η⁻¹≡id ⟩
       (   ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵗ idᵗ
  ≡⟨ ∘ᵗ-identityʳ _ ⟩
       ⟨⟩-≤ (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))
    ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) 0))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ 0 ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ∎
-}
env-ctx-time-⟨⟩-nat {.(_ ⟨ τ + τ' ⟩)} {.((_ ⟨ _ ⟩) ⟨ _ ⟩)} {A} (⟨⟩-μ-ren {Γ} {τ} {τ'}) = 
  begin
       (   ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) (τ + τ')))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ τ + τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (+-comm τ τ'))
    ∘ᵗ μ {⟦ Γ ⟧ᵉᵒ A}
  ≡⟨ {!!} ⟩
       ⟨⟩-≤ {A} (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))
    ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ)))
    ∘ᵗ ⟨ τ' ⟩ᶠ (μ {A})
    ∘ᵗ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-∘ᵗ _ _))))) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))
    ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (   ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ)))
    ∘ᵗ ⟨ τ' ⟩ᶠ (   μ {A}
                ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-∘ᵗ _ _)))) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))
    ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ + τ) τ'))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (   ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
                ∘ᵗ μ {A}
                ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
  ∎
env-ctx-time-⟨⟩-nat {.((_ ⟨ _ ⟩) ⟨ _ ⟩)} {.(_ ⟨ τ + τ' ⟩)} (⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'}) = {!!}
env-ctx-time-⟨⟩-nat {.(_ ⟨ _ ⟩)} {.(_ ⟨ _ ⟩)} {A} (⟨⟩-≤-ren {Γ} {τ} {τ'} p) =
  {!!}
{-
  begin
       (   ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} p
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
    ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} p
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (
      begin
           ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
        ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} p
      ≡⟨ ⟨⟩-≤-nat _ _ ⟩
           ⟨⟩-≤ {⟨ ctx-time Γ ⟩ᵒ A} p
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ _) ⟩
           idᵗ
        ∘ᵗ ⟨⟩-≤ {⟨ ctx-time Γ ⟩ᵒ A} p
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym ⟨⟩-idᵗ) ⟩
           ⟨ τ ⟩ᶠ idᵗ
        ∘ᵗ ⟨⟩-≤ {⟨ ctx-time Γ ⟩ᵒ A} p
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (≡-≡ᵗ (cong ⟨ τ ⟩ᶠ (≡ᵗ-≡ ⟨⟩-≤-refl)))) ⟩
           ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} ≤-refl)
        ∘ᵗ ⟨⟩-≤ {⟨ ctx-time Γ ⟩ᵒ A} p
        ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
      ∎)) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} ≤-refl)
    ∘ᵗ ⟨⟩-≤ {⟨ ctx-time Γ ⟩ᵒ A} p
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵗ-congʳ
      (≡ᵗ-trans
        (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))
        (≡ᵗ-sym (∘ᵗ-assoc _ _ _))) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ (   μ {A}
        ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} ≤-refl)
        ∘ᵗ ⟨⟩-≤ {⟨ ctx-time Γ ⟩ᵒ A} p)
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-μ-≤ p ≤-refl))) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ (   ⟨⟩-≤ {A} (+-mono-≤ p ≤-refl)
        ∘ᵗ μ {A})
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ≡ᵗ-trans (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
       (   ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵗ ⟨⟩-≤ {A} (+-mono-≤ p ≤-refl))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵗ-congˡ (⟨⟩-≤-trans _ _) ⟩
       ⟨⟩-≤ {A} (≤-trans (≤-reflexive (+-comm (ctx-time Γ) τ)) (+-mono-≤ p ≤-refl))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵗ-congˡ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
       ⟨⟩-≤ {A} (≤-trans (+-monoʳ-≤ (ctx-time Γ) p) (≤-reflexive (+-comm (ctx-time Γ) τ')))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _)) ⟩
       (   ⟨⟩-≤ {A} (+-monoʳ-≤ (ctx-time Γ) p)
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ')))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       ⟨⟩-≤ {A} (+-monoʳ-≤ (ctx-time Γ) p)
    ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ'))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ' ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
  ∎
-}
env-ctx-time-⟨⟩-nat {.(_ ∷ _)} {.(_ ∷ _)} {A} (cong-∷-ren {Γ} {Γ'} {B} ρ) =
  {!!}
{-
  begin
       (env-ctx-time-⟨⟩ Γ ∘ᵗ fstᵗ)
    ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       env-ctx-time-⟨⟩ Γ
    ∘ᵗ fstᵗ
    ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
  ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _) ⟩
       env-ctx-time-⟨⟩ Γ
    ∘ᵗ ⟦ ρ ⟧ʳ {A}
    ∘ᵗ fstᵗ
  ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
       (   env-ctx-time-⟨⟩ Γ
        ∘ᵗ ⟦ ρ ⟧ʳ {A})
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (env-ctx-time-⟨⟩-nat ρ) ⟩
       (   ⟨⟩-≤ {A} (ren-≤-ctx-time ρ)
        ∘ᵗ env-ctx-time-⟨⟩ Γ')
    ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       ⟨⟩-≤ {A} (ren-≤-ctx-time ρ)
    ∘ᵗ env-ctx-time-⟨⟩ Γ'
    ∘ᵗ fstᵗ
  ∎
-}
env-ctx-time-⟨⟩-nat {.(_ ⟨ _ ⟩)} {.(_ ⟨ _ ⟩)} {A} (cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ) =
  {!!}
{-
  begin
       (   ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵗ μ {A}
        ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ))
    ∘ᵗ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ ≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)
    ∘ᵗ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩-∘ᵗ _ _))) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ ∘ᵗ ⟦ ρ ⟧ʳ)
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡-≡ᵗ (cong ⟨ τ ⟩ᶠ (≡ᵗ-≡ (env-ctx-time-⟨⟩-nat ρ))))) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ μ {A}
    ∘ᵗ (⟨ τ ⟩ᶠ (⟨⟩-≤ {A} (ren-≤-ctx-time ρ) ∘ᵗ env-ctx-time-⟨⟩ Γ'))
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (⟨⟩-∘ᵗ _ _)) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} (ren-≤-ctx-time ρ))
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ (   μ {A}
        ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} (ren-≤-ctx-time ρ)))
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ
      (begin
        μ {A} ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} (ren-≤-ctx-time ρ))
      ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityʳ _)) ⟩
        μ {A} ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} (ren-≤-ctx-time ρ)) ∘ᵗ idᵗ
      ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym ⟨⟩-≤-refl)) ⟩
        μ {A} ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {A} (ren-≤-ctx-time ρ)) ∘ᵗ ⟨⟩-≤ {⟨ _ ⟩ᵒ A} ≤-refl
      ≡⟨ ≡ᵗ-sym (⟨⟩-μ-≤ _ _) ⟩
        ⟨⟩-≤ {A} (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ)) ∘ᵗ μ {A}
      ∎)) ⟩
       ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
    ∘ᵗ (  ⟨⟩-≤ {A} (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ))
       ∘ᵗ μ {A})
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ≡ᵗ-sym
      (≡ᵗ-trans
        (∘ᵗ-assoc _ _ _)
        (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))) ⟩
       (⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
        ∘ᵗ ⟨⟩-≤ {A} (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ)))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵗ-congˡ (⟨⟩-≤-trans _ _) ⟩
       ⟨⟩-≤ {A} (≤-trans (≤-reflexive (+-comm (ctx-time Γ) τ)) (+-mono-≤ ≤-refl (ren-≤-ctx-time ρ)))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵗ-congˡ (≡-≡ᵗ (cong ⟨⟩-≤ (≤-irrelevant _ _))) ⟩
       ⟨⟩-≤ {A} (≤-trans (+-monoˡ-≤ τ (ren-≤-ctx-time ρ)) (≤-reflexive (+-comm (ctx-time Γ') τ)))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-trans _ _)) ⟩
       (   ⟨⟩-≤ {A} (+-monoˡ-≤ τ (ren-≤-ctx-time ρ))
        ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ') τ)))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
       ⟨⟩-≤ {A} (+-monoˡ-≤ τ (ren-≤-ctx-time ρ))
    ∘ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ') τ))
    ∘ᵗ μ {A}
    ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ')
  ∎
-}
