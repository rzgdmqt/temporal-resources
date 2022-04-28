-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Function

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Semantics.TSets
open import Semantics.Modality.Past
open import Semantics.Interpretation

open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Renamings where

-- Semantics of renamings as maps between environments

⟦_⟧ʳ : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → ⟦ Γ' ⟧ᵉ →ᵗ ⟦ Γ ⟧ᵉ
⟦ id-ren ⟧ʳ =
  idᵗ
⟦ ρ' ∘ʳ ρ ⟧ʳ =
  ⟦ ρ ⟧ʳ ∘ᵗ ⟦ ρ' ⟧ʳ
⟦ wk-ren ⟧ʳ =
  fstᵗ
⟦ var-ren x ⟧ʳ =
  ⟨ idᵗ ,    ε-⟨⟩
          ∘ᵗ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
          ∘ᵗ var-in-env x ⟩ᵗ
⟦ ⟨⟩-η-ren ⟧ʳ =
  η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ =
  η⁻¹
⟦ ⟨⟩-μ-ren {Γ} {τ} {τ'} ⟧ʳ =
     ⟨⟩-≤ {A = ⟦ Γ ⟧ᵉ} (≤-reflexive (+-comm τ τ'))
  ∘ᵗ μ {A = ⟦ Γ ⟧ᵉ}
⟦ ⟨⟩-≤-ren {Γ} p ⟧ʳ =
  ⟨⟩-≤ {A = ⟦ Γ ⟧ᵉ} p
⟦ cong-∷-ren ρ ⟧ʳ =
  mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
⟦ cong-⟨⟩-ren {Γ} {Γ'} {τ} ρ ⟧ʳ =
  ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ

-- Relating syntactic wk-⟨⟩-ctx-ren and semantic split-env-⟨⟩

z≤n≡≤-refl : z≤n ≡ ≤-refl {0}
z≤n≡≤-refl = ≤-irrelevant _ _

wk-⟨⟩-ctx≡split-env-≤ : ∀ {Γ Γ' Γ'' τ}
                      → (p : Γ' , Γ'' split Γ)
                      → (q : τ ≤ ctx-time Γ'')
                      → ⟦ wk-⟨⟩-ctx-ren p q ⟧ʳ
                     ≡ᵗ    ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q
                        ∘ᵗ env-ctx-time-⟨⟩ Γ''
                        ∘ᵗ split-env p
                     
wk-⟨⟩-ctx≡split-env-≤ {Γ' = Γ'} split-[] z≤n =
  begin
    η
   ≡⟨ ≡ᵗ-sym (∘ᵗ-identityˡ η) ⟩
     idᵗ ∘ᵗ η
   ≡⟨ ∘ᵗ-congˡ η (≡ᵗ-sym (⟨⟩-≤-refl {⟦ Γ' ⟧ᵉ})) ⟩
     ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} ≤-refl ∘ᵗ η
   ≡⟨ ∘ᵗ-congˡ η (⟨⟩-≤-≡ {⟦ Γ' ⟧ᵉ} ≤-refl z≤n) ⟩
     ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} z≤n ∘ᵗ η
   ≡⟨ ≡ᵗ-sym (∘ᵗ-identityʳ (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} z≤n ∘ᵗ η)) ⟩
     ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} z≤n ∘ᵗ η ∘ᵗ idᵗ
   ∎

wk-⟨⟩-ctx≡split-env-≤ (split-∷ p) q = {!!}

wk-⟨⟩-ctx≡split-env-≤ (split-⟨⟩ p) q = {!!}
