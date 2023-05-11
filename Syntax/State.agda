{-# OPTIONS --allow-unsolved-metas #-}
module Syntax.State where

open import Util.Time
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Syntax.Renamings

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 



mutual 
    data 𝕊 : (τ : Time) → Set where
        ∅ : 𝕊 0
        _⟨_⟩ₘ : {τ' : Time} → 𝕊 τ' → (τ'' : Time) → 𝕊 (τ' + τ'') 
        _∷ₘ[_]_ : {τ : Time} {A : VType} → (S : 𝕊 τ) → (τ' : Time) → (toCtx S) ⟨ τ' ⟩ ⊢V⦂ A → 𝕊 τ 

    toCtx : {τ : Time} → 𝕊 τ → Ctx
    toCtx ∅ = []
    toCtx (S ⟨ τ'' ⟩ₘ) = (toCtx S) ⟨ τ'' ⟩
    toCtx (_∷ₘ[_]_ {A = A₁} S τ' A) = (toCtx S) ∷ [ τ' ] A₁

-- Relation that tells that S' is a successor of S
data SucState : {τ τ' : Time} → τ ≤ τ' → 𝕊 τ → 𝕊 τ' → Set where
    id-suc : {τ : Time} → {S : 𝕊 τ} → SucState ≤-refl S S
    ⟨⟩-suc : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → (p : τ ≤ τ') → (τ'' : Time) → 
        SucState p S S' → SucState (≤-stepsʳ τ'' p) S (S' ⟨ τ'' ⟩ₘ)
    ∷-suc : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → {A : VType} → 
        (p : τ ≤ τ') → (τ'' : Time) → (V : (toCtx S') ⟨ τ'' ⟩ ⊢V⦂ A) → 
        SucState p S S' → SucState p S (S' ∷ₘ[ τ'' ] V)

SucState⇒Ren : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → (p : τ ≤ τ') → SucState p S S' → Ren (toCtx S) (toCtx S')
SucState⇒Ren .≤-refl id-suc = id-ren
SucState⇒Ren .(≤-stepsʳ τ'' p) (⟨⟩-suc p τ'' sucState) = wk-⟨⟩-ren ∘ʳ SucState⇒Ren p sucState
SucState⇒Ren p (∷-suc .p τ'' V sucState) = wk-ren ∘ʳ SucState⇒Ren p sucState

time-pass : ∀ {τ} → (S : 𝕊 τ) → (τ' : Time) → 𝕊 (τ + τ')
time-pass S τ = S ⟨ τ ⟩ₘ 

extend-state : ∀ {τ A} → (S : 𝕊 τ) → (τ' : Time) → (V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A) → 𝕊 τ
extend-state S τ' V = S ∷ₘ[ τ' ] V 

τ-subst-state : ∀ {τ τ'} → (p : τ ≡ τ') → (S : 𝕊 τ) → 𝕊 τ'
τ-subst-state refl S = S 


record Config (C : CType) : Set where
    constructor ⟨_,_,_⟩
    field
        τ : Time
        state : 𝕊 τ
        computation : toCtx state ⊢C⦂ C
