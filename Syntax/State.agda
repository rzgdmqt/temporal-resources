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

data SucState : {τ τ' : Time} → 𝕊 τ → 𝕊 τ' → Set where
    id-suc : {τ : Time} → {S : 𝕊 τ} → SucState S S
    ⟨⟩-suc : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → (p : τ ≤ τ') → (τ'' : Time) → 
        SucState S S' → SucState S (S' ⟨ τ'' ⟩ₘ)
    ∷-suc : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → {A : VType} → 
        (p : τ ≤ τ') → (τ'' : Time) → (V : (toCtx S') ⟨ τ'' ⟩ ⊢V⦂ A) → 
        SucState S S' → SucState S (S' ∷ₘ[ τ'' ] V)

SucState⇒Ren : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → (p : τ ≤ τ') → SucState S S' → Ren (toCtx S) (toCtx S')
SucState⇒Ren p id-suc = id-ren
SucState⇒Ren p (⟨⟩-suc p₁ τ'' y) = wk-⟨⟩-ren ∘ʳ (SucState⇒Ren p₁ y)
SucState⇒Ren p (∷-suc p₁ τ'' V y) = wk-ren ∘ʳ (SucState⇒Ren p₁ y)

τ-≤-subst : ∀ {τ τ' τ''} → τ ≤ τ' → τ' ≡ τ'' → τ ≤ τ''
τ-≤-subst p refl = p

in-past-state : {τ τ' τ'' τ''' τ'''' : Time} → 
                {A : VType} → 
                {S : 𝕊 τ} → 
                {S' : 𝕊 τ'} →  
                (p : τ ≤ τ') →  
                SucState S S' →  
                (M : toCtx S ⟨ τ'' ⟩ ⊢C⦂ A ‼ τ'''') →
                (q : τ + τ'' ≤ τ' + τ''') →  
                toCtx S' ⟨ τ''' ⟩ ⊢C⦂ A ‼ τ''''
in-past-state {τ} {S = S} {S' = .S} p id-suc M q = C-rename (⟨⟩-≤-ren (+-cancelˡ-≤ τ q)) M
in-past-state {τ} {τ'} {τ''} {τ'''} {S = S} {S' = .(_ ⟨ τ₁ ⟩ₘ)} p (⟨⟩-suc {τ' = τ₂} p₁ τ₁ sucSS') M q = 
        C-rename ⟨⟩-μ-ren (in-past-state p₁ sucSS' M (τ-≤-subst q (+-assoc τ₂ τ₁ τ''')))  
in-past-state {S = S} {S' = .(_ ∷ₘ[ τ'' ] V)} p (∷-suc p₁ τ'' V sucSS') M q = 
        C-rename (cong-⟨⟩-ren wk-ren) (in-past-state p sucSS' M q) 

suc-comp-ren : {τ τ' τ'' τ''' τ'''' : Time} → 
                {A : VType} → 
                {S : 𝕊 τ} → 
                {S' : 𝕊 τ'} →  
                (p : τ ≤ τ') →  
                SucState S S' →  
                (M : toCtx S ⟨ τ'' ⟩ ⊢C⦂ A ‼ τ'''') →
                (q : τ + τ'' ≤ τ' + τ''') →  
                Ren (toCtx S ⟨ τ'' ⟩) (toCtx S' ⟨ τ''' ⟩)
suc-comp-ren {τ} p id-suc M q = ⟨⟩-≤-ren (+-cancelˡ-≤ τ q)
suc-comp-ren {τ} {τ'} {τ'' = τ₂} {τ'''} p (⟨⟩-suc {τ' = τ₃} p₁ τ'' sucSS') M q = 
        ⟨⟩-μ-ren ∘ʳ suc-comp-ren p₁ sucSS' M (τ-≤-subst q (+-assoc τ₃ τ'' τ'''))
suc-comp-ren p (∷-suc p₁ τ'' V sucSS') M q = cong-⟨⟩-ren wk-ren ∘ʳ 
        suc-comp-ren p sucSS' M q 

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
