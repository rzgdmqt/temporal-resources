module Syntax.TheoremsAboutSteps where


open import Util.Time
open import Syntax.Types
open import Syntax.PerservationTheorem
open import Syntax.Language
open import Syntax.State

-- Theorem that step only extends state

step-extends-state : {τ τ' τ'' τ''' : Time} → 
                {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ ) → 
                SucState S S'
step-extends-state APP = id-suc
step-extends-state MATCH = id-suc
step-extends-state SEQ-RET = id-suc
step-extends-state SEQ-OP = id-suc
step-extends-state HANDLE-RET = id-suc
step-extends-state (UNBOX p) = id-suc 
step-extends-state HANDLE-OP = id-suc
step-extends-state DELAY = ⟨⟩-suc ≤-refl _ id-suc
step-extends-state BOX = ∷-suc ≤-refl _ _ id-suc
step-extends-state (SEQ-FST {M = M} {M₁ = M'} τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = step-extends-state  M↝M'
step-extends-state (HANDLE-STEP {M = M} {M₁ = M'} τ≤τ₇ τ+τ₄≡τ₇+τ₆ sucState M↝M') = step-extends-state M↝M'

-- Theorem that step only increases time

step-increases-time : {τ τ' τ'' τ''' : Time} → 
                {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ ) → 
                τ ≤ τ'
step-increases-time APP = ≤-refl
step-increases-time MATCH = ≤-refl
step-increases-time SEQ-RET = ≤-refl
step-increases-time SEQ-OP = ≤-refl
step-increases-time HANDLE-RET = ≤-refl
step-increases-time HANDLE-OP = ≤-refl
step-increases-time BOX = ≤-refl
step-increases-time (UNBOX p) = ≤-refl
step-increases-time (DELAY {τ' = τ'}) = ≤-stepsʳ τ' ≤-refl
step-increases-time (SEQ-FST τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState x) = τ≤τ₁
step-increases-time (HANDLE-STEP τ≤τ₇ τ+τ₄≡τ₇+τ₆ sucState x) = τ≤τ₇


