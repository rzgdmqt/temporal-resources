module OperationalSemantics.TheoremsAboutSteps where


open import Util.Time
open import Syntax.Types
open import OperationalSemantics.PerservationTheorem
open import Syntax.Language
open import OperationalSemantics.State
open import Util.Operations
open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

-- Theorem that step only extends state

step-extends-state : {τ τ' τ'' τ''' : Time} → 
                {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ ) → 
                S ≤ₛ S'
step-extends-state APP = id-suc
step-extends-state MATCH = id-suc
step-extends-state SEQ-RET = id-suc
step-extends-state SEQ-OP = id-suc
step-extends-state HANDLE-RET = id-suc
step-extends-state (UNBOX p) = id-suc 
step-extends-state HANDLE-OP = id-suc
step-extends-state DELAY = ⟨⟩-suc _ id-suc
step-extends-state BOX = ∷-suc _ _ id-suc
step-extends-state (SEQ-FST {M = M} {M₁ = M'} τ+τ₂≡τ₁+τ₄ S≤ₛS' M↝M') = step-extends-state  M↝M'
step-extends-state (HANDLE-STEP {M = M} {M₁ = M'} τ+τ₄≡τ₇+τ₆ S≤ₛS' M↝M') = step-extends-state M↝M'

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
step-increases-time (SEQ-FST τ+τ₂≡τ₁+τ₄ S≤ₛS' x) = S≤ₛS'⇒τ≤τ' S≤ₛS'
step-increases-time (HANDLE-STEP τ+τ₄≡τ₇+τ₆ S≤ₛS' x) = S≤ₛS'⇒τ≤τ' S≤ₛS'

-- step perserves overall time

conf-time+comp-time≡const : ∀ {A τ τ' τ'' τ'''}
                → {S : 𝕊 τ}
                → {S' : 𝕊 τ'}
                → {M : toCtx S ⊢C⦂ A ‼ τ''}
                → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
                → ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩
                → τ + τ'' ≡ τ' + τ'''
conf-time+comp-time≡const APP = refl
conf-time+comp-time≡const MATCH = refl
conf-time+comp-time≡const {τ = τ} {τ'} (SEQ-FST {τ₂ = τ₂} {τ₃} {τ₄} τ+τ₂≡τ₁+τ₄ S≤ₛS' M↝M') = 
     begin 
        τ + (τ₂ + τ₃) ≡⟨ sym (+-assoc τ τ₂ τ₃) ⟩  
        τ + τ₂ + τ₃ ≡⟨ cong (_+ τ₃) τ+τ₂≡τ₁+τ₄ ⟩  
        τ' + τ₄ + τ₃ ≡⟨ +-assoc τ' τ₄ τ₃ ⟩  
        τ' + (τ₄ + τ₃)
    ∎
conf-time+comp-time≡const SEQ-RET = refl
conf-time+comp-time≡const SEQ-OP = refl
conf-time+comp-time≡const {τ = τ} {τ''' = τ'''} (DELAY {τ' = τ'}) = 
    sym (+-assoc τ τ' τ''')
conf-time+comp-time≡const HANDLE-RET = refl
conf-time+comp-time≡const {τ = τ} {τ'} (HANDLE-STEP {τ₁ = τ₁} {τ₂ = τ₂} {τ₃} τ+τ₂≡τ₄+τ₃ S≤ₛS' M↝M') = 
    begin 
        τ + (τ₂ + τ₁) ≡⟨ sym (+-assoc τ τ₂ τ₁) ⟩  
        τ + τ₂ + τ₁ ≡⟨ cong (_+ τ₁) τ+τ₂≡τ₄+τ₃ ⟩  
        τ' + τ₃ + τ₁ ≡⟨ +-assoc τ' τ₃ τ₁ ⟩  
        τ' + (τ₃ + τ₁)
    ∎
conf-time+comp-time≡const {τ = τ} (HANDLE-OP {τ' = τ'} {τ'' = τ''} {op = op}) = 
    cong (τ +_) (+-assoc (op-time op) τ'' τ')
conf-time+comp-time≡const BOX = refl
conf-time+comp-time≡const (UNBOX p) = refl
