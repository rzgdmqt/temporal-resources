module Syntax.ProgressTheorem where


open import Util.Time
open import Util.Properties
open import Syntax.TheoremsAboutSteps
open import Syntax.PerservationTheorem
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Syntax.State
open import Util.Operations
open import Util.Equality
open import Data.Empty

-- Progress theorem. A term is either returned value, operation or makes step

data progresses : {τ' τ : Time} → 
                {S : 𝕊 τ} → 
                {A : VType} → 
                (M : toCtx S ⊢C⦂ A ‼ τ') →  Set where
                            
    is-value : {τ : Time} → 
            {S : 𝕊 τ} → 
            {A : VType} → 
            {V : toCtx S ⊢V⦂ A} →
            ---------------------
            progresses (return V) 
    
    is-op : {τ τ' : Time} → 
            {S : 𝕊 τ} → 
            {A : VType} → 
            {op : Op} → 
            {V : toCtx S ⊢V⦂ type-of-gtype (param op) } → 
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ'} → 
            --------------------------------------------------------------------
            progresses (perform op V M) 


    steps : {τ τ' τ'' τ''' : Time} → (q : τ ≤ τ') → 
            {S : 𝕊 τ} {S' : 𝕊 τ'} {A : VType} → 
            {M : toCtx S ⊢C⦂ A ‼ τ''} →
            {M' : toCtx S' ⊢C⦂  A ‼ τ''' } → 
            (p : τ + τ'' ≡ τ' + τ''') → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ →
            ----------------------------------
            progresses M 

progress : {τ τ' : Time} {S : 𝕊 τ} {A : VType} → (M : toCtx S ⊢C⦂ A ‼ τ') → progresses M 
progress (return V) = is-value
progress {τ} {τ'} {S = S} {A = A} ((_;_) {τ' = τ₁} M N) with progress M
... | is-value = steps ≤-refl refl SEQ-RET 
... | is-op = steps ≤-refl refl (SEQ-OP {S = S})
... | steps {τ' = τ₂} {τ'' = τ₃} {τ''' = τ₄} p q M↝M' = 
    steps p (step-time-eq τ τ₃ τ₁ τ₂ τ₄ q) (SEQ-FST q p (step-extends-state M↝M') M↝M')
progress {τ} {τ'} {S} (lam M · V) = steps ≤-refl refl APP
progress {τ} {τ'} (delay {τ' = τ₁} τ₂ M ) = 
    steps (≤-stepsʳ τ₂ ≤-refl) (sym (+-assoc τ τ₂ τ₁)) DELAY
progress (match ⦉ V , W ⦊ `in M) = steps ≤-refl refl MATCH
progress (perform op V M) = is-op
progress {τ} (handle_`with_`in {τ' = τ₁} M H N) with progress M 
... | is-value = steps ≤-refl refl HANDLE-RET
... | is-op {τ' = τ'} {op = op} = 
        steps ≤-refl (τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ τ (op-time op) τ' τ₁) HANDLE-OP
... | steps {τ' = τ₂} {τ'' = τ₃} {τ''' = τ₄} p q M↝M' = 
    steps p (step-time-eq τ τ₃ τ₁ τ₂ τ₄ q) (HANDLE-STEP p q (step-extends-state M↝M') M↝M')
progress (unbox τ≤ctx-time V M) = steps ≤-refl refl (UNBOX τ≤ctx-time)
progress (box V M) = steps ≤-refl refl BOX
progress (absurd (var V)) = ⊥-elim (Empty-not-in-ctx V)
progress (var V · N) = ⊥-elim (⇒-not-in-ctx V)
progress (match var V `in M) = ⊥-elim (⦉⦊-not-in-ctx V)


-- Theorem: is-value is indeed final state (make no further steps)

finality-value : ∀ {A B τ τ₁ τ₂}
                → {S : 𝕊 τ}
                → {S₁ : 𝕊 τ₁}
                → {V : toCtx S ⊢V⦂ A}
                → progresses (return V)
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₂}
                → ⟨ τ , S , return V ⟩ ↝ ⟨ τ₁ , S₁ , M₁ ⟩
                → ⊥
finality-value is-value ()


-- Theorem: is-op is indeed final state (make no further steps)

finality-op : ∀ {A B op τ τ₁ τ₂ τ₃}
                → {S : 𝕊 τ}
                → {S₁ : 𝕊 τ₁}
                → {V : toCtx S ⊢V⦂ type-of-gtype (param op) }
                → {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ₂}
                → progresses (perform op V M)
                → {M₁ : toCtx S₁ ⊢C⦂ B ‼ τ₃}
                → ⟨ τ , S , perform op V M ⟩ ↝ ⟨ τ₁ , S₁ , M₁ ⟩
                → ⊥
finality-op is-op ()