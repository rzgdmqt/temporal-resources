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

-- Relating syntactic wk-⟨⟩-ctx-ren and semantic split-env

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
   ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩-≤-refl {⟦ Γ' ⟧ᵉ})) ⟩
     ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} ≤-refl ∘ᵗ η
   ≡⟨ ∘ᵗ-congˡ (⟨⟩-≤-≡ {⟦ Γ' ⟧ᵉ} ≤-refl z≤n) ⟩
     ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} z≤n ∘ᵗ η
   ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-identityʳ η)) ⟩
     ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} z≤n ∘ᵗ η ∘ᵗ idᵗ
   ∎

wk-⟨⟩-ctx≡split-env-≤ {Γ' = Γ'} {Γ'' = Γ'' ∷ A} (split-∷ p) q = 
  begin
    ⟦ wk-⟨⟩-ctx-ren p q ⟧ʳ ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-congˡ (wk-⟨⟩-ctx≡split-env-≤ p q) ⟩
    (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q ∘ᵗ (env-ctx-time-⟨⟩ Γ'' ∘ᵗ split-env p)) ∘ᵗ fstᵗ
  ≡⟨ ∘ᵗ-assoc (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q) (env-ctx-time-⟨⟩ Γ'' ∘ᵗ split-env p) fstᵗ ⟩
    ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q ∘ᵗ ((env-ctx-time-⟨⟩ Γ'' ∘ᵗ split-env p) ∘ᵗ fstᵗ)
  ≡⟨ ∘ᵗ-congʳ {h = ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q} (∘ᵗ-assoc (env-ctx-time-⟨⟩ Γ'') (split-env p) fstᵗ) ⟩
    ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q ∘ᵗ (env-ctx-time-⟨⟩ Γ'' ∘ᵗ (split-env p ∘ᵗ fstᵗ))
  ≡⟨ ∘ᵗ-congʳ {h = ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q}
       (∘ᵗ-congʳ {h = env-ctx-time-⟨⟩ Γ''}
         (≡ᵗ-sym (⟨⟩ᵗ-fstᵗ (split-env p ∘ᵗ fstᵗ) (idᵗ ∘ᵗ sndᵗ)))) ⟩
    ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q ∘ᵗ (env-ctx-time-⟨⟩ Γ'' ∘ᵗ (fstᵗ ∘ᵗ mapˣᵗ (split-env p) idᵗ))
  ≡⟨ ∘ᵗ-congʳ {h = ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q}
       (≡ᵗ-sym (∘ᵗ-assoc (env-ctx-time-⟨⟩ Γ'') fstᵗ (mapˣᵗ (split-env p) idᵗ))) ⟩
    ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q ∘ᵗ (env-ctx-time-⟨⟩ Γ'' ∘ᵗ fstᵗ) ∘ᵗ mapˣᵗ (split-env p) idᵗ
  ∎

wk-⟨⟩-ctx≡split-env-≤ {Γ' = Γ'} {Γ'' = Γ'' ⟨ τ ⟩} {τ = τ'} (split-⟨⟩ p) q =
  begin
         (   ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ)
          ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ))
          ∘ᵗ μ {⟦ Γ' ⟧ᵉ})
      ∘ᵗ ⟨ τ ⟩ᶠ ⟦ wk-⟨⟩-ctx-ren p (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ))) ⟧ʳ
   ≡⟨ ∘ᵗ-congʳ {h = ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ) ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ)) ∘ᵗ μ {⟦ Γ' ⟧ᵉ}}
         (⟨⟩-≡
           (wk-⟨⟩-ctx≡split-env-≤ p
             (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ)))))
    ⟩
         (   ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ)
          ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ))
          ∘ᵗ μ {⟦ Γ' ⟧ᵉ})
      ∘ᵗ ⟨ τ ⟩ᶠ (   ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ)))
                 ∘ᵗ env-ctx-time-⟨⟩ Γ''
                 ∘ᵗ split-env p)
   ≡⟨ ∘ᵗ-congʳ {h = ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ) ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ)) ∘ᵗ μ {⟦ Γ' ⟧ᵉ}}
         (⟨⟩-∘
           (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ))))
           (env-ctx-time-⟨⟩ Γ'' ∘ᵗ split-env p))
    ⟩
         (   ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ)
          ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ))
          ∘ᵗ μ {⟦ Γ' ⟧ᵉ})
      ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ))))
      ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ'' ∘ᵗ split-env p)
   ≡⟨ ∘ᵗ-congʳ {h = ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ) ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ)) ∘ᵗ μ {⟦ Γ' ⟧ᵉ}}
        (∘ᵗ-congʳ {h = ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ))))}
          (⟨⟩-∘ (env-ctx-time-⟨⟩ Γ'') (split-env p)))
    ⟩
         (   ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (n≤n∸m+m τ' τ)
          ∘ᵗ ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (τ' ∸ τ) τ))
          ∘ᵗ μ {⟦ Γ' ⟧ᵉ})
      ∘ᵗ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-trans (∸-monoˡ-≤ τ q) (≤-reflexive (m+n∸n≡m (ctx-time Γ'') τ))))
      ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ'')
      ∘ᵗ ⟨ τ ⟩ᶠ (split-env p)
   ≡⟨ {!!}
    ⟩
        ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} q
     ∘ᵗ (   ⟨⟩-≤ {⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (ctx-time Γ'') τ))
         ∘ᵗ μ {⟦ Γ' ⟧ᵉ}
         ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ''))
     ∘ᵗ ⟨ τ ⟩ᶠ (split-env p)
   ∎
