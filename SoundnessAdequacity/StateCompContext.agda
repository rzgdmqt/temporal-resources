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
    → Γ ⊢K[ state ◁ Ctx→Bctx (toCtx S) ⊢ A ‼ τ ]⦂ (A ‼ (ctx-time (toCtx S) + τ))
    
toK ∅ =
  []ₖ
toK {A = A} {τ = τ'} (S ⟨ τ ⟩ₛ) =
  (τ-substK (sym (+-assoc _ τ τ')) (toK {A = A} {τ = τ + τ' } S)) [ delay[ f≤ᶠf ]ₖ τ []ₖ ]ₖ
toK (_∷ₛ_ {τ = τ} S V) =
  (toK S) [ box[ f≤ᶠf ]ₖ (V-rename (eq-ren (cong (_⟨ τ ⟩) (sym (⋈-++ₗ-[] _ (toCtx S))))) V) []ₖ ]ₖ 

-- Spliting computation term context at resource 
{-
split-K : ∀ {Γ A B C D τ τ' τ'' τ''' τ''''}
        → (S : 𝕊 Γ)
        → (x : [ τ ] A ∈[ τ' ] toCtx S)
        → (K : Γ ⊢K[ state ◁ Ctx→Bctx (proj₁ (var-split x)) ++ₗ [ τ ] A ∷ₗ Ctx→Bctx (proj₁ (proj₂ (var-split x))) ⊢ C ‼ τ''' ]⦂ B ‼ τ'') 
        → Σ[ K₁ ∈ Γ ⊢K[ state ◁ Ctx→Bctx (proj₁ (var-split x)) ⊢ D ‼ τ'''' ]⦂ B ‼ τ'' ] 
          (Σ[ K₂ ∈ 
            ((Γ ⋈ (Ctx→Bctx (proj₁ (var-split x)))) ∷ [ τ ] A) 
              ⊢K[ state ◁ Ctx→Bctx (proj₁ (proj₂ (var-split x))) ⊢ C ‼ τ''' ]⦂ D ‼ τ'''' ] 
            K₁ [ box[ f≤ᶠf ]ₖ 
                (V-rename 
                   ((cong-⟨⟩-ren 
                   (eq-ren (sym (trans 
                     ((Γ⋈Δ≡Γ++ᶜctxΔ Γ (Ctx→Bctx (proj₁ (var-split x))))) 
                     (cong (Γ ++ᶜ_) 
                     (trans 
                       (Ctx→Bctx→Ctx-iso (proj₁ (var-split x))) 
                       (sym (fst-split-state≡split-ctx S x)))))))))
                (resource-lookup S x)) K₂ ]ₖ ≡  K )
split-K S x K = {!   !}
-}
