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
env-ctx-time-⟨⟩-nat {Γ} {.(Γ ∷ _)} wk-ren = {!!}
env-ctx-time-⟨⟩-nat {.(Γ' ∷ _)} {Γ'} (var-ren x) = {!!}
env-ctx-time-⟨⟩-nat {.(Γ' ⟨ 0 ⟩)} {Γ'} ⟨⟩-η-ren = {!!}
env-ctx-time-⟨⟩-nat {Γ} {.(Γ ⟨ 0 ⟩)} ⟨⟩-η⁻¹-ren = {!!}
env-ctx-time-⟨⟩-nat {.(_ ⟨ τ + τ' ⟩)} {.((_ ⟨ _ ⟩) ⟨ _ ⟩)} (⟨⟩-μ-ren {τ = τ} {τ' = τ'}) = {!!}
env-ctx-time-⟨⟩-nat {.((_ ⟨ _ ⟩) ⟨ _ ⟩)} {.(_ ⟨ τ + τ' ⟩)} (⟨⟩-μ⁻¹-ren {τ = τ} {τ' = τ'}) = {!!}
env-ctx-time-⟨⟩-nat {.(_ ⟨ _ ⟩)} {.(_ ⟨ _ ⟩)} (⟨⟩-≤-ren x) = {!!}
env-ctx-time-⟨⟩-nat {.(_ ∷ _)} {.(_ ∷ _)} (cong-∷-ren ρ) = {!!}
env-ctx-time-⟨⟩-nat {.(_ ⟨ _ ⟩)} {.(_ ⟨ _ ⟩)} (cong-⟨⟩-ren ρ) = {!!}



{-

env-ctx-time-⟨⟩ : (Γ : Ctx)
                → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵗ ⟨ ctx-time Γ ⟩ᵒ A

-}
