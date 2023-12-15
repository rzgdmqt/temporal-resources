module SoundnessAdequacity.StateCompContext where

open import Syntax.CompContext
open import OperationalSemantics.State

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Types
open import Syntax.Renamings


open import Util.Equality
open import Util.Operations
open import Util.Time
open import Data.Empty
open import Data.Product
open import Data.Sum


-- Translating states to computation term contexts

mutual

  toK : ∀ {Γ A τ}
      → (S : 𝕊 Γ)
      → Γ ⊢K[ state ◁ A ‼ τ ]⦂ (A ‼ (state-time S + τ))
      
  toK ∅ =
    []ₖ
  toK {A = A} {τ = τ'} (S ⟨ τ ⟩ₛ) =
    τ-substK (sym (+-assoc _ τ τ')) ((toK S) [ delay[ f≤ᶠf ]ₖ τ []ₖ ]ₖ)
  toK {Γ} (_∷ₛ_ {A = A} {τ = τ} S V) =
    (toK S) [ box[ f≤ᶠf ]ₖ
      (V-rename (eq-ren (cong (λ Γ' → (Γ ++ᶜ Γ') ⟨ τ ⟩) (trans (sym ++ᶜ-identityˡ) (toCtx-rel-hole-ctx S)))) V) []ₖ ]ₖ

  postulate {- TODO: temporarily postulated -}
    toCtx-rel-hole-ctx : ∀ {Γ Γ' A τ}
                       → (S : 𝕊 Γ)
                       → Γ' ++ᶜ toCtx S ≡ rel-hole-ctx (toK {A = A} {τ = τ} S) Γ'

  {-
  toCtx-rel-hole-ctx {Γ} {Γ'} {A} {τ} ∅ = refl
  toCtx-rel-hole-ctx {Γ} {Γ'} {A} {τ} (S ⟨ τ' ⟩ₛ) =
    trans
      (cong (_⟨ τ' ⟩) (toCtx-rel-hole-ctx {A = A} {τ = τ} S))
      (trans
        (cong (λ K → rel-hole-ctx K Γ' ⟨ τ' ⟩) (τ-substK-[·]ₖ {!!} (toK S) []ₖ))
        {!!})
  toCtx-rel-hole-ctx {Γ} {Γ'} {A} {τ} (S ∷ₛ V) = {!!}
  -}
