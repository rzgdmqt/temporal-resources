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
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Relation.Nullary

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
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
    data 𝕊 : (τ : Time) → Set where
        ∅ : 𝕊 0
        _⟨_⟩ₘ : {τ' : Time} → 𝕊 τ' → (τ'' : Time) → 𝕊 (τ' + τ'') 
        _∷ₘ[_]_ : {τ : Time} {A : VType} → (S : 𝕊 τ) → (τ' : Time) → (toCtx S) ⟨ τ' ⟩ ⊢V⦂ A → 𝕊 τ 

    toCtx : {τ : Time} → 𝕊 τ → Ctx
    toCtx ∅ = []
    toCtx (S ⟨ τ'' ⟩ₘ) = (toCtx S) ⟨ τ'' ⟩
    toCtx (_∷ₘ[_]_ {A = A₁} S τ' A) = (toCtx S) ∷ [_]_ τ' A₁

-- subst transport resp (HOTT)
τ-subst-state : ∀ {τ τ'} → (p : τ ≡ τ') → (S : 𝕊 τ) → 𝕊 τ'
τ-subst-state refl S = S 

time-pass : ∀ {τ} → (S : 𝕊 τ) → (τ' : Time) → 𝕊 (τ + τ')
time-pass S τ = S ⟨ τ ⟩ₘ 

extend-state : ∀ {τ A} → (S : 𝕊 τ) → (τ' : Time) → (V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A) → 𝕊 τ
extend-state S τ' V = S ∷ₘ[ τ' ] V 

-- resource-use : ∀ {τ τ' τ'' A} → (S : 𝕊 τ) → 
--                 (p : τ' ≤ τ'') → 
--                 (q : ([ τ' ] A) ∈[ τ'' ] toCtx S) →  
--                 toCtx S ⊢V⦂ A
-- resource-use {τ} {τ'} {τ''} {A} S p q = {!   !}


resource-use : ∀ {τ τ' A} → (S : 𝕊 τ) → 
                (p : τ' ≤ ctx-time (toCtx S)) → 
                (V : toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A) →  
                toCtx S ⊢V⦂ A
resource-use {A} S p V with toCtx S 
... | [] = ⊥-elim {!   !}
... | Γ ∷ hd = {!   !}
... | Γ ⟨ τ ⟩ = {!   !}

record Config (C : CType) : Set where
    constructor ⟨_,_,_⟩
    field
        τ : Time
        state : 𝕊 τ
        computation : toCtx state ⊢C⦂ C

-- ask this here. How to specify fields
-- τ-subst-config : ∀ {C τ τ'} → {S : 𝕊 τ} → {M : toCtx S  ⊢C⦂ C} → (p : τ ≡ τ') → {!   !} → {!   !}
-- τ-subst-config {τ = τ} {τ' = τ'} refl ⟨ τ , S , M ⟩ = {!   !} 

data _↝_ :  {C D : CType} → Config C → Config D → Set where
    
    APP :   {A B : VType} {τ τ' : Time} 
            {S : 𝕊 τ} → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ τ'} → {V : (toCtx S) ⊢V⦂ A} →
            -------------------------------------------------------------
            ⟨ τ , S , lam M · V ⟩ ↝ ⟨ τ , S , M [ Hd ↦ V ]c ⟩

    MATCH : {τ : Time} {S : 𝕊 τ} {A B : VType} {C : CType} → 
            {V : toCtx S ⊢V⦂ A } →
            {W : toCtx S ⊢V⦂ B } → 
            {M : toCtx S ∷ A ∷ B ⊢C⦂ C} → 
            -------------------------------------------------------
            ⟨ τ , S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
            ⟨ τ , S , (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟩
    
    SEQ-FST : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : Time} → (p : τ₁ ≤ τ₂) → 
            {A B : VType} → {S : 𝕊 τ} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
            {N : ((toCtx S) ⟨ τ₂ ⟩ ∷ A) ⊢C⦂ B ‼ τ₃} → 
            {M' : toCtx S ⟨ τ₁ ⟩ ⊢C⦂ A ‼ τ₄} →
            (q : τ₂ ≡ τ₁ + τ₄) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ + τ₁ , S ⟨ τ₁ ⟩ₘ  , M' ⟩ → 
            --------------------------------------------------------------------
            ⟨ τ , S , M ; N ⟩ ↝ 
            ⟨ τ + τ₁ , time-pass S τ₁ , M' ; 
                C-rename (cong-∷-ren ⟨⟩-μ-ren) (τ-subst⟨⟩ q N) ⟩ 

    SEQ-RET : {τ τ' : Time} → 
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
            ⟨ τ , S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ τ + τ' , time-pass S τ' , M ⟩

    BOX :   {τ τ' τ'' : Time} → {S : 𝕊 τ} → {A B : VType} → 
            {V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A} →  
            {M : toCtx S ∷ [_]_ τ' A ⊢C⦂ B ‼ τ''} →
            -----------------------------------------------------------------------
            ⟨ τ , S , (box V M) ⟩ ↝ ⟨ τ , extend-state S τ' V , M ⟩

    UNBOX : {τ τ' : Time} → {S : 𝕊 τ} →  {A : VType} → {C : CType} → 
            (p : τ' ≤ ctx-time (toCtx S)) → 
            {V : (toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)} → 
            {M : toCtx S ∷ A ⊢C⦂ C } → 
            ---------------------------------------------------------------------------------------------
            -- ⟨ τ , S , unbox p V M ⟩ ↝ ⟨ τ , S , M  [ Hd ↦ V-rename (-ᶜ-⟨⟩-ren τ' p) (resource-use V) ]c ⟩
            ⟨ τ , S , unbox p V M ⟩ ↝ ⟨ τ , S , M [ Hd ↦ resource-use S p V ]c ⟩


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

    steps : {τ τ' τ'' τ''' : Time} → (q : τ ≤ τ') → 
            {S : 𝕊 τ} {S' : 𝕊 τ'} {A : VType} → 
            {M : toCtx S ⊢C⦂ A ‼ τ''} →
            {M' : toCtx S' ⊢C⦂  A ‼ τ''' } → 
            (p : τ + τ'' ≡ τ' + τ''') → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ →
            ----------------------------------
            progresses M 

τ≡τ∸τ'+τ' : ∀ τ τ' → τ ∸ (τ' ∸ τ') ≡ τ
τ≡τ∸τ'+τ' τ τ' = 
    begin 
        τ ∸ (τ' ∸ τ') ≡⟨ cong (τ ∸_) (n∸n≡0 τ') ⟩  
        τ ∸ 0 ≡⟨ refl ⟩ 
        τ
    ∎

lemma : ∀ τ τ' τ₁ → τ ≤ τ₁ → τ + τ + (τ₁ ∸ τ + τ') ≡ τ + (τ₁ + τ')
lemma τ τ' τ₁ p = 
    begin 
        τ + τ + (τ₁ ∸ τ + τ') ≡⟨ +-assoc τ τ (τ₁ ∸ τ + τ') ⟩  
        τ + (τ + (τ₁ ∸ τ + τ')) ≡⟨ cong (τ +_ ) (cong (τ +_) ( sym (+-∸-comm τ' p))) ⟩ 
        τ + (τ + (τ₁ + τ' ∸ τ)) ≡⟨ cong (τ +_ ) (cong (τ +_) (cong (_∸ τ) (+-comm τ₁ τ')) ) ⟩ 
        τ + (τ + (τ' + τ₁ ∸ τ)) ≡⟨ cong (τ +_ ) (cong (τ +_) (+-∸-assoc τ' p)) ⟩ 
        τ + (τ + (τ' + (τ₁ ∸ τ))) ≡⟨ cong (τ +_ ) (sym (+-assoc τ τ' (τ₁ ∸ τ))) ⟩ 
        τ + (τ + τ' + (τ₁ ∸ τ)) ≡⟨ cong (τ +_) (cong (_+ (τ₁ ∸ τ)) (+-comm τ τ')) ⟩
        τ + (τ' + τ + (τ₁ ∸ τ)) ≡⟨ cong (τ +_)  (+-assoc τ' τ (τ₁ ∸ τ))  ⟩
        τ + (τ' + (τ + (τ₁ ∸ τ))) ≡⟨ cong (τ +_) (cong (τ' +_) (a+b∸a≡b {a = τ } {b = τ₁} {p = p})) ⟩
        τ + (τ' + τ₁) ≡⟨ cong (τ +_) (+-comm τ' τ₁) ⟩
        τ + (τ₁ + τ')
    ∎


⇒-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} {A : VType} {C : CType} → A ⇒ C ∈[ τ' ] toCtx S → ⊥
⇒-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ x) = ⇒-not-in-ctx x
⇒-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x₁} (Tl-∷ x) = ⇒-not-in-ctx x

⦉⦊-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} {A B : VType} → A |×| B ∈[ τ' ] toCtx S → ⊥
⦉⦊-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ y) = ⦉⦊-not-in-ctx y
⦉⦊-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x} (Tl-∷ y) = ⦉⦊-not-in-ctx y

Empty-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} → Empty ∈[ τ' ] toCtx S → ⊥
Empty-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ y) = Empty-not-in-ctx y
Empty-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x} (Tl-∷ y) = Empty-not-in-ctx y 


progress : {τ τ' : Time} {S : 𝕊 τ} {A : VType} → (M : toCtx S ⊢C⦂ A ‼ τ') → progresses M 
progress (return V) = is-value
progress {τ} {τ'} (M ; N) with progress M
... | is-value = steps ≤-refl refl SEQ-RET 
... | steps {τ} {τ'} {τ''} {τ'''} p q M↝M' = steps (≤-stepsʳ (τ' ∸ τ) ≤-refl) {!   !} (SEQ-FST {!   !} {!   !} {! M↝M'!}) 
progress {τ} {τ'} {S} (lam M · V) = steps ≤-refl refl APP
progress {τ} {τ'} (delay {τ' = τ₁} τ₂ M ) = steps (≤-stepsʳ τ₂ ≤-refl) (sym (+-assoc τ τ₂ τ₁)) DELAY
progress (match ⦉ V , W ⦊ `in M) = steps ≤-refl refl MATCH
progress (perform op V M) = {!   !}
progress (handle M `with H `in N) with progress M 
... | is-value = {! !}
... | steps p q M↝M' = {!   !}
progress (unbox τ≤ctx-time V M) = steps ≤-refl refl (UNBOX τ≤ctx-time)
progress (box V M) = steps ≤-refl refl BOX
progress (absurd (var V)) = ⊥-elim (Empty-not-in-ctx V)
progress (var V · N) = ⊥-elim (⇒-not-in-ctx V)
progress (match var V `in M) = ⊥-elim (⦉⦊-not-in-ctx V)
 