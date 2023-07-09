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