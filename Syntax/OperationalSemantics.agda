module Syntax.OperationalSemantics where

open import Util.Time
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Util.Operations
open import Util.Equality
open import Data.Nat.Base
open import Syntax.Substitutions



mutual 
    data 𝕊 (τ : Time) : Set where
        ∅ : 𝕊 τ
        _⟨_⟩ₘ : {τ' τ'' : Time} → 𝕊 τ' → (τ'' : Time) → {τ' + τ'' ≡ τ} → 𝕊 τ 
        _∷ₘ_ : {A : VType} → (Γ : 𝕊 τ) → (toCtx Γ) ⊢V⦂ A → 𝕊 τ

    toCtx : {τ : Time} → 𝕊 τ → Ctx
    toCtx {τ = τ} ∅  = [] ⟨ τ ⟩
    toCtx (σ ⟨ τ'' ⟩ₘ) = (toCtx σ) ⟨ τ'' ⟩
    toCtx {τ = τ} (_∷ₘ_ {A'} σ A) = (toCtx σ) ∷ A'
        
 
record Triple (A : CType) : Set where
    constructor ⟨_,_,_⟩
    field
        τ : Time
        state : 𝕊 τ
        computation : toCtx state ⊢C⦂ A

data _↝_ : {C D : CType} → Triple C → Triple D → Set where
    APP :   {A : VType} {B : CType} {τ : Time} 
            {S : 𝕊 τ} {M : ((toCtx S) ∷ A) ⊢C⦂ B} {N : (toCtx S) ⊢V⦂ A} →
            -------------------------------------------------------------
            ⟨ τ , S , lam M · N ⟩ ↝ ⟨ τ , S , M [ Hd ↦ N ]c ⟩
    
    -- to be continued ...
