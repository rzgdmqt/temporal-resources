module Syntax.Semisoundness where

open import Syntax.EquationalTheory
open import Syntax.PerservationTheorem
open import Syntax.ProgressTheorem
open import Syntax.Types
open import Syntax.Contexts
open import Syntax.CompContext
open import Syntax.Language
open import Syntax.State
open import Syntax.Renamings
open import Syntax.Substitutions

open import Util.Equality
open import Util.Time
open import Util.Properties

config-to-comp : ∀ {A τ} 
        → (Cf : Config (A ‼ τ)) 
        → (S : 𝕊 (Config.τ Cf))  -- this and next line are just to fix termination error in Agda
        → S ≡ Config.state Cf 
        → [] ⊢C⦂ A ‼ (τ + Config.τ Cf)
config-to-comp {τ = τ} ⟨ .0 , ∅ , M ⟩ _ _ = τ-subst (sym (+-identityʳ τ)) M
config-to-comp {τ = τ'} ⟨ .(τ + τ'') , _⟨_⟩ₘ {τ} S τ'' , M ⟩ .(S ⟨ τ'' ⟩ₘ) refl = 
    τ-subst (0+[τ''+τ'+τ]≡τ'+[τ+τ''] τ τ' τ'') 
        (delay 0 
            (C-rename wk-⟨⟩-ren 
            (config-to-comp ⟨ τ , S , delay τ'' M ⟩ S refl)))
config-to-comp ⟨ τ , S ∷ₘ[ τ' ] X , M ⟩ (.S ∷ₘ[ .τ' ] .X) refl = 
    config-to-comp ⟨ τ , S , box X M ⟩ S refl


step-induces-equationaly-equal-computations : ∀ {A τ τ' τ'' τ'''}
        → {S : 𝕊 τ} 
        → {S' : 𝕊 τ'}
        → {M : toCtx S ⊢C⦂ A ‼ τ''}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
        → (τ''+τ≡τ'''+τ' : τ'' + τ ≡ τ''' + τ')
        → (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ )
        → [] ⊢C⦂ 
            τ-subst τ''+τ≡τ'''+τ' (config-to-comp ⟨ τ , S , M ⟩ S refl)
            == 
            config-to-comp ⟨ τ' , S' , M' ⟩ S' refl
step-induces-equationaly-equal-computations p APP = {!   !}
step-induces-equationaly-equal-computations p MATCH = {!   !}
step-induces-equationaly-equal-computations p (SEQ-FST τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = {!   !}
step-induces-equationaly-equal-computations p SEQ-RET = {!   !}
step-induces-equationaly-equal-computations p SEQ-OP = {!   !}
step-induces-equationaly-equal-computations p DELAY = {!   !}
step-induces-equationaly-equal-computations p HANDLE-RET = {!   !}
step-induces-equationaly-equal-computations p (HANDLE-STEP τ≤τ₄ τ+τ₂≡τ₄+τ₃ sucState M↝M') = {!   !}
step-induces-equationaly-equal-computations p HANDLE-OP = {!   !}
step-induces-equationaly-equal-computations p BOX = {!   !}
step-induces-equationaly-equal-computations p (UNBOX p₁) = {!   !}