module Syntax.OperationalSemantics where

open import Util.Time
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Util.Operations
open import Util.Equality
open import Data.Nat.Base
open import Syntax.Substitutions
open import Syntax.Renamings

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

τ-subst⟨⟩ : ∀ {Γ A B τ τ' τ''}
        → τ ≡ τ'
        → Γ ⟨ τ ⟩ ∷ B ⊢C⦂ A ‼ τ''
        --------------------------
        → Γ ⟨ τ' ⟩ ∷ B ⊢C⦂ A ‼ τ''

τ-subst⟨⟩ refl M = M


a+b∸a≡b : ∀ {a b} → {p : a ≤ b} → a + (b ∸ a) ≡ b 
a+b∸a≡b {a} {b} {p} = 
    begin 
        a + (b ∸ a) ≡⟨ sym (+-∸-assoc a p) ⟩ 
        (a + b) ∸ a ≡⟨ +-∸-comm {m = a} b {o = a} ≤-refl ⟩ 
        (a ∸ a) + b ≡⟨ cong (_+ b) (n∸n≡0 a) ⟩  
        0 + b 
    ∎

mutual 
    data 𝕊 (τ : Time) : Set where
        ∅ : 𝕊 τ
        _⟨_⟩ₘ : {τ' : Time} → 𝕊 τ' → (τ'' : Time) → {τ' + τ'' ≡ τ} → 𝕊 τ 
        _∷ₘ_ : {A : VType} → (S : 𝕊 τ) → (toCtx S) ∷ A ⊢V⦂ A → 𝕊 τ -- is this ok? 

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

data _↝_ :  {C D : CType} → Triple C → Triple D → Set where
    
    APP :   {A : VType} {B : CType} {τ : Time} 
            {S : 𝕊 τ} {M : ((toCtx S) ∷ A) ⊢C⦂ B} {V : (toCtx S) ⊢V⦂ A} →
            -------------------------------------------------------------
            ⟨ τ , S , lam M · V ⟩ ↝ ⟨ τ , S , M [ Hd ↦ V ]c ⟩
    
    SEQ_FST : {τ τ' τ'' τ''' : Time} → {p : τ' ≤ τ''} → 
            {A B : VType} → {S : 𝕊 τ} → 
            {M : toCtx S ⊢C⦂ A ‼ τ''} → 
            {N : ((toCtx S) ⟨ τ'' ⟩ ∷ A) ⊢C⦂ B ‼ τ'''} → 
            {M' : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ (τ'' ∸ τ')} → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ + τ' , _⟨_⟩ₘ {τ = τ + τ'} S  τ' {refl} , M' ⟩ → 
            --------------------------------------------------------------------
            ⟨ τ , S , M ; N ⟩ ↝ 
            ⟨ τ + τ' , _⟨_⟩ₘ {τ = τ + τ'} S  τ' {refl} , 
            M' ; ( C-rename (cong-∷-ren ( ⟨⟩-μ-ren )) (τ-subst⟨⟩ (sym (a+b∸a≡b {τ'} {τ''} {p})) N)) ⟩ 

    SEQ_RET : {τ τ' : Time} → 
            {A B : VType} → {S : 𝕊 τ} → 
            {V : (toCtx S) ⊢V⦂ A} 
            {N : ((toCtx S) ⟨ 0 ⟩ ∷ A) ⊢C⦂ B ‼ τ'} →  
            -----------------------------------------------------------------------------------
            ⟨ τ , S , return V ; N ⟩ ↝ ⟨ τ , S , C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟩
                
    DELAY : {τ τ' τ'' : Time} → 
            {S : 𝕊 τ} →
            {A : VType} →  
            {M : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ τ''} → 
            -------------------------------------------------------------------------------------
            ⟨ τ , S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ τ + τ' , _⟨_⟩ₘ {τ = τ + τ'} S τ' {refl} , M ⟩

    BOX :   {τ τ' τ'' : Time} → {S : 𝕊 τ} → {A B : VType} → 
            {V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A} →  
            {M : toCtx S ∷ [_]_ τ' A ⊢C⦂ B ‼ τ''} →
            -----------------------------------------------------------------------
            ⟨ τ , S , (box V M) ⟩ ↝ ⟨ τ , S ∷ₘ var {A = [_]_ τ' A} {τ = 0} Hd , M ⟩

    UNBOX : {τ τ' : Time} → {S : 𝕊 τ} →  {A : VType} → {C : CType} → 
            {p : τ' ≤ ctx-time (toCtx S)} → 
            {V : (toCtx S -ᶜ τ' ⊢V⦂ [_]_ τ' A)} → 
            {M : toCtx S ∷ A ⊢C⦂ C } → 
            -----------------------------------------------------------------------
            ⟨ τ , S , unbox p V M ⟩ ↝ ⟨ τ , S , M  [ {!  Hd !} ↦ V ]c ⟩

-- should we add absurd constructor and op?
data progresses : {τ τ' : Time} → 
                {S : 𝕊 τ} {A : VType} → 
                (M : toCtx S ⊢C⦂ A ‼ τ') →  Set where
    is-value : {τ : Time} {S : 𝕊 τ} {A : VType} → 
            {V : toCtx S ⊢V⦂ A} →
            ---------------------
            progresses (return V) 
    steps : {τ τ' τ'' : Time} → {τ ≤ τ'} → 
            {S : 𝕊 τ} {S' : 𝕊 τ'} {A : VType} → 
            {M : toCtx S ⊢C⦂ A ‼ τ''} →
            {M' : toCtx S' ⊢C⦂  A ‼ (τ'' ∸ (τ' ∸ τ)) } → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ →
            ------------
            progresses M 


progress : {τ τ' : Time} {S : 𝕊 τ} {A : VType} → (M : toCtx S ⊢C⦂ A ‼ τ') → progresses M 
progress (return V) = is-value
progress (M ; N) with progress M -- maybe special case for operation performing? 
... | is-value = steps {! SEQ_RET  !}
... | steps M↝M' = steps {! SEQ_FST  !}  
progress (lam V · N) = steps {! APP !}
progress (var V · N) = {!   !} -- this shouldn't be the case
progress (delay τ M ) = steps {! DELAY  !}
progress (match var V `in M) = {!   !} -- this shouldn't be the case
progress (match ⦉ V₁ , V₂ ⦊ `in M) = {!   !}
progress (absurd V) = {!   !}
progress (perform op V M) = {!   !}
progress (handle M `with H `in N) with progress M 
... | is-value = {! HANDLE_RET  !}
... | steps M↝M' = {!   !}
progress (unbox τ≤ctx-time V M) = steps {!  UNBOX !}
progress (box V M) = steps {!  BOX !}