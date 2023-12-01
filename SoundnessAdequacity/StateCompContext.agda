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

toK : ∀ {Γ A τ}
    → (S : 𝕊 Γ)
    → Γ ⊢K[ state ◁ Ctx→Bctx (toCtx S) ⊢ A ‼ τ ]⦂ (A ‼ (state-time S + τ))
    
toK ∅ =
  []ₖ
toK {A = A} {τ = τ'} (S ⟨ τ ⟩ₛ) =
  (τ-substK (sym (+-assoc _ τ τ')) (toK {A = A} {τ = τ + τ' } S)) [ delay[ f≤ᶠf ]ₖ τ []ₖ ]ₖ
toK (_∷ₛ_ {τ = τ} S V) =
  (toK S) [ box[ f≤ᶠf ]ₖ (V-rename (eq-ren (cong (_⟨ τ ⟩) (sym (⋈-++ₗ-[] _ (toCtx S))))) V) []ₖ ]ₖ

-- Spliting computation term context at resource 

{-
split-state-K : ∀ {Γ A B τ τ' τ''}
              → (S : 𝕊 Γ)
              → (x : [ τ ] A ∈[ τ' ] toCtx S)
              → let p   = (sym (trans (Γ⋈Δ≡Γ++ᶜctxΔ Γ (Ctx→Bctx (toCtx (split-state-fst S x)))) (cong (Γ ++ᶜ_) (Ctx→Bctx→Ctx-iso _)))) in
                let K   = subst₂
                            (λ Δ τ → Γ ⊢K[ state ◁ Δ ⊢ B ‼ τ'' ]⦂ (B ‼ τ))
                            {!!}
                            {!!}
                            (toK {A = B} {τ = τ''} S) in
                let K'  = toK (split-state-fst S x) in
                let V   = subst
                            (λ Γ → Γ ⟨ τ ⟩ ⊢V⦂ A)
                            p
                            (resource-lookup S x) in
                let K'' = subst
                            (λ Γ → Γ ∷ [ τ ] A ⊢K[ state ◁ Ctx→Bctx (toCtx (split-state-snd S x)) ⊢ B ‼ τ'' ]⦂ (B ‼ (state-time (split-state-snd S x) + τ'')))
                            p
                            (toK {A = B} {τ = τ''} (split-state-snd S x)) in
                K ≡ K' [ box[ f≤ᶠf ]ₖ V K'' ]ₖ

split-state-K S x = {!!}
-}
