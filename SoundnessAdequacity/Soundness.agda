module SoundnessAdequacity.Soundness where

open import SoundnessAdequacity.StateCompContext
open import Syntax.CompContext

open import OperationalSemantics.State
open import OperationalSemantics.ProgressTheorem
open import OperationalSemantics.PerservationTheorem

open import EquationalTheory.EquationalTheory

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.Types

open import Util.Equality
open import Data.Empty
open import Util.Operations
open import Data.Product
open import Util.Time


-- Soundness theorem

soundness : ∀ {A B τ₁ τ₂ τ₃}
        → {S S' : 𝕊 []} 
        → {M : toCtx S ⊢C⦂ A ‼ τ₁}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ₂}
        → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → let S≤ₛS' = step-extends-state M↝M' in 
        let suc-part-state = (suc-part-state S S' S≤ₛS') in 
        (E : toCtx S ⊢K[ eval ◁ []ₗ ⊢ A ‼ τ₁ ]⦂ B ‼ τ₃)
        → let p = sym (trans (⋈-identityˡ {Δ = Ctx→Bctx (toCtx S)}) (Ctx→Bctx→Ctx-iso (toCtx S))) in
        let q = eq-ren (sym (trans 
                (⋈-identityˡ {Δ = Ctx→Bctx (toCtx S) ++ₗ []ₗ}) 
                (trans {j = BCtx→Ctx (Ctx→Bctx (toCtx S))} 
                  (cong BCtx→Ctx (Ctx→Bctx-hom (toCtx S) [])) 
                  (Ctx→Bctx→Ctx-iso (toCtx S))))) in 
        let r = eq-ren (sym (trans 
                (⋈-identityˡ {Δ = Ctx→Bctx (toCtx S) ++ₗ Ctx→Bctx (toCtx suc-part-state)}) 
                (trans 
                  (cong BCtx→Ctx (Ctx→Bctx-hom (toCtx S) (toCtx suc-part-state))) 
                  (trans 
                    (Ctx→Bctx→Ctx-iso ((toCtx S) ++ᶜ (toCtx suc-part-state))) 
                    (S++suc-partS≡S' S S' S≤ₛS'))))) in
        let s = trans ++ᶜ-identityˡ p in
        let t = second-part-equality 
                  (ctx-time (toCtx S')) 
                  (ctx-time (toCtx S)) 
                  (ctx-time (toCtx suc-part-state)) 
                  τ₁ τ₂ 
                  (sym (trans 
                    (sym (ctx-time-++ᶜ (toCtx S) (toCtx suc-part-state))) 
                    (time-S++suc-partS≡S' S S' S≤ₛS')))
                  (trans 
                    (cong (_+ τ₁) (sym (time-≡ S))) 
                    (trans 
                      (proj₂ (perservation-theorem M↝M')) 
                      (cong (_+ τ₂) (time-≡ S')))) in
        ------------------------------------------------------------
        [] ⊢C⦂ 
            (toK S [ Γ-substK p E ]ₖ) [ C-rename q M ]
          == 
            ((toK S' [ {!K-rename ? E!} ]ₖ) [ C-rename {!r!} M' ] )
soundness M↝M' E = {!   !}

-- TODO: define K-rename, replace with K-rename eq-ren

--(((toK S) [ (Γ-substK p E) [ Γ-substK s {!!} ]ₖ ]ₖ) [ (C-rename r M') ])

-- Γ-substK s ((τ-substK t (toK suc-part-state)))


soundness' : ∀ {A B τ₁ τ₂ τ₃}
        → {S S' : 𝕊 []} 
        → {M : toCtx S ⊢C⦂ A ‼ τ₁}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ₂}
        → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → let S≤ₛS' = step-extends-state M↝M' in 
        let suc-part-state = (suc-part-state S S' S≤ₛS') in 
        (E : toCtx S ⊢K[ eval ◁ []ₗ ⊢ A ‼ τ₁ ]⦂ B ‼ τ₃)
        → let p = sym (trans (⋈-identityˡ {Δ = Ctx→Bctx (toCtx S)}) (Ctx→Bctx→Ctx-iso (toCtx S))) in
        let q = eq-ren (sym (trans 
                (⋈-identityˡ {Δ = Ctx→Bctx (toCtx S) ++ₗ []ₗ}) 
                (trans {j = BCtx→Ctx (Ctx→Bctx (toCtx S))} 
                  (cong BCtx→Ctx (Ctx→Bctx-hom (toCtx S) [])) 
                  (Ctx→Bctx→Ctx-iso (toCtx S))))) in 
        let r = eq-ren (sym (trans 
                (⋈-identityˡ {Δ = Ctx→Bctx (toCtx S) ++ₗ Ctx→Bctx (toCtx suc-part-state)}) 
                (trans 
                  (cong BCtx→Ctx (Ctx→Bctx-hom (toCtx S) (toCtx suc-part-state))) 
                  (trans 
                    (Ctx→Bctx→Ctx-iso ((toCtx S) ++ᶜ (toCtx suc-part-state))) 
                    (S++suc-partS≡S' S S' S≤ₛS'))))) in
        let s = trans ++ᶜ-identityˡ p in
        let t = second-part-equality 
                  (ctx-time (toCtx S')) 
                  (ctx-time (toCtx S)) 
                  (ctx-time (toCtx suc-part-state)) 
                  τ₁ τ₂ 
                  (sym (trans 
                    (sym (ctx-time-++ᶜ (toCtx S) (toCtx suc-part-state))) 
                    (time-S++suc-partS≡S' S S' S≤ₛS')))
                  (trans 
                    (cong (_+ τ₁) (sym (time-≡ S))) 
                    (trans 
                      (proj₂ (perservation-theorem M↝M')) 
                      (cong (_+ τ₂) (time-≡ S')))) in
        [] ⊢C⦂ 
            (toK S [ Γ-substK p E ]ₖ) [ C-rename q M ]
          == 
            (((toK S) [ (Γ-substK p E) [ Γ-substK s (τ-substK t (toK suc-part-state)) ]ₖ ]ₖ) [ (C-rename r M') ])
soundness' M↝M' E = {!   !}
