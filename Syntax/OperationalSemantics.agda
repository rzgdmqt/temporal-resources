{-# OPTIONS --allow-unsolved-metas #-}
module Syntax.OperationalSemantics where


open import Util.Time
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Syntax.State
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

τ-subst : ∀ {Γ A τ τ'}
        → τ ≡ τ'
        → Γ ⊢C⦂ A ‼ τ
        ---------------
        → Γ ⊢C⦂ A ‼ τ'

τ-subst refl M = M

a+b∸a≡b : ∀ {a b} → {p : a ≤ b} → a + (b ∸ a) ≡ b 
a+b∸a≡b {a} {b} {p} = 
    begin 
        a + (b ∸ a) ≡⟨ sym (+-∸-assoc a p) ⟩ 
        (a + b) ∸ a ≡⟨ +-∸-comm {m = a} b {o = a} ≤-refl ⟩ 
        (a ∸ a) + b ≡⟨ cong (_+ b) (n∸n≡0 a) ⟩  
        0 + b 
    ∎

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


m≡n⇒m≤n : ∀ {m n} → m ≡ n → m ≤ n
m≡n⇒m≤n {zero} {n} p = z≤n
m≡n⇒m≤n {suc m} {suc n} p = s≤s (m≡n⇒m≤n (suc-injective p))

⇒-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} {A : VType} {C : CType} → A ⇒ C ∈[ τ' ] toCtx S → ⊥
⇒-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ x) = ⇒-not-in-ctx x
⇒-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x₁} (Tl-∷ x) = ⇒-not-in-ctx x

⦉⦊-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} {A B : VType} → A |×| B ∈[ τ' ] toCtx S → ⊥
⦉⦊-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ y) = ⦉⦊-not-in-ctx y
⦉⦊-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x} (Tl-∷ y) = ⦉⦊-not-in-ctx y

Empty-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} → Empty ∈[ τ' ] toCtx S → ⊥
Empty-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ y) = Empty-not-in-ctx y
Empty-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x} (Tl-∷ y) = Empty-not-in-ctx y 

not-in-empty-ctx : {τ : Time} {A : VType} → A ∈[ τ ] [] → ⊥
not-in-empty-ctx ()


-- resource-use : ∀ {τ τ' τ'' A} → (S : 𝕊 τ) → 
--                 (p : τ' ≤ τ'') → 
--                 (q : ([ τ' ] A) ∈[ τ'' ] toCtx S) →  
--                 toCtx S ⊢V⦂ A
-- resource-use {τ} {τ'} {τ''} {A} S p q = {!   !}

resource-use : ∀ {τ τ' A} → (S : 𝕊 τ) → 
                (p : τ' ≤ ctx-time (toCtx S)) →
                (V : toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A) →
                toCtx S ⊢V⦂ A
resource-use {τ = τ} ∅ p (var x) = ⊥-elim (not-in-empty-ctx {τ = τ} {! !})
resource-use (S ⟨ τ'' ⟩ₘ) p V = {!   !}
resource-use {τ} {τ'} (S ∷ₘ[ τ'' ] x) p V =  {!   !} [ Hd ↦ V-rename (-ᶜ-⟨⟩-ren τ' p ∘ʳ wk-⟨⟩-ren {τ = τ'}) V ]v


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
    
    SEQ-FST : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : Time} → 
            {A B : VType} → {S : 𝕊 τ} → {S₁ : 𝕊 τ₁} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
            {N : ((toCtx S) ⟨ τ₂ ⟩ ∷ A) ⊢C⦂ B ‼ τ₃} → 
            {M' : toCtx S₁ ⊢C⦂ A ‼ τ₄} →
            (τ+τ₂≡τ₁+τ₄ : τ + τ₂ ≡ τ₁ + τ₄) →  
            (τ≤τ₁ : τ ≤ τ₁) → 
            (sucState : SucState (S ⟨ τ₂ ⟩ₘ) (S₁ ⟨ τ₄ ⟩ₘ)) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ₁ , S₁ , M' ⟩ →
            --------------------------------------------------------------------
            ⟨ τ , S , M ; N ⟩ ↝ 
            ⟨ τ₁ , S₁ , M' ; (C-rename (cong-∷-ren (  SucState⇒Ren (m≡n⇒m≤n τ+τ₂≡τ₁+τ₄) sucState)) N) ⟩ 

    SEQ-RET : {τ τ' : Time} → 
            {A B : VType} → {S : 𝕊 τ} → 
            {V : (toCtx S) ⊢V⦂ A} 
            {N : ((toCtx S) ⟨ 0 ⟩ ∷ A) ⊢C⦂ B ‼ τ'} →  
            -----------------------------------------------------------------------------------
            ⟨ τ , S , return V ; N ⟩ ↝ ⟨ τ , S , C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟩
    
    SEQ-OP : {τ τ' τ'' : Time} → 
            {S : 𝕊 τ''} → 
            {op : Op} → 
            {A B : VType} → {S : 𝕊 τ''} → 
            {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ} →  
            {N : toCtx S ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
            -----------------------------------------------------------------------------------
            ⟨ τ'' , S , perform op V M ; N  ⟩ ↝ ⟨ τ'' , S ,  τ-subst (sym (+-assoc (op-time op) τ τ'))
                         (perform op V
                            (M ;
                             C-rename 
                             (cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} 
                                wk-ren ∘ʳ cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren)
                             N))  ⟩
    
    DELAY : {τ τ' τ'' : Time} → 
            {S : 𝕊 τ} →
            {A : VType} →  
            {M : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ τ''} → 
            ---------------------------------------------------------------------
            ⟨ τ , S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ τ + τ' , time-pass S τ' , M ⟩

    HANDLE-RET : {τ τ' : Time} →
            {S : 𝕊 τ} → 
            {A B : VType} → 
            {V : toCtx S ⊢V⦂ A} →
            {H : (op : Op) → (τ'' : Time) →
                toCtx S ∷ type-of-gtype (param op)
                  ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                ⊢C⦂ B ‼ (op-time op + τ'')} → 
            {N : toCtx S ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
            --------------------------------------------------------------------------
            ⟨ τ , S , handle return V `with H `in N ⟩ ↝ 
            ⟨ τ , S , (C-rename (cong-∷-ren ⟨⟩-η-ren) N) [ Hd ↦ V ]c ⟩ 
    
    HANDLE-STEP : {A B : VType} →
            {τ τ₁ τ₂ τ₄ τ₅ τ₆ τ₇ : Time} → 
            {S : 𝕊 τ} → 
            {S₁ : 𝕊 τ₇} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₄} → 
            {H : (op : Op) → 
                 (τ₃ : Time) →
                 toCtx S ∷ type-of-gtype (param op)
                   ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₃)
                 ⊢C⦂ B ‼ (op-time op + τ₃)} → 
            {N : toCtx S ⟨ τ₄ ⟩ ∷ A ⊢C⦂ B ‼ τ₁} → 
            {M' : toCtx S₁  ⊢C⦂ A ‼ τ₆ } →  
            (τ≤τ₇ : τ ≤ τ₇) → 
            (τ+τ₄≡τ₇+τ₆ : τ + τ₄ ≡ τ₇ + τ₆) → 
            (sucState₁ : SucState S S₁) → 
            (sucState₂ : SucState (S ⟨ τ₄ ⟩ₘ) (S₁ ⟨ τ₆ ⟩ₘ)) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ₇ , S₁ , M' ⟩ → 
            -----------------------------------------------------------------------
            ⟨ τ , S , handle M `with H `in N ⟩ ↝ 
            ⟨ τ₇ , S₁ , handle M' 
                        `with 
                            (λ op τ'' → C-rename (cong-∷-ren (cong-∷-ren (SucState⇒Ren τ≤τ₇ sucState₁))) (H op τ'')) 
                        `in (C-rename (cong-∷-ren (SucState⇒Ren (m≡n⇒m≤n τ+τ₄≡τ₇+τ₆) sucState₂)) N) ⟩
    
    -- HANDLE-OP : {τ τ' τ'' : Time} →
    --         {S : 𝕊 τ} → 
    --         {op : Op} → 
    --         {A B : VType} → 
    --         {V : toCtx S ⊢V⦂ type-of-gtype (param op)} →
    --         {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ''} →
    --         {H : (op : Op) → (τ'' : Time) →
    --             toCtx S ∷ type-of-gtype (param op)
    --               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
    --             ⊢C⦂ B ‼ (op-time op + τ'')} → 
    --         {N : toCtx S ⟨ op-time op + τ'' ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
    --         --------------------------------------------------------------------------
    --         ⟨ τ , S , handle perform op V M `with H `in N ⟩ ↝ 
    --         ⟨ τ , S , 
    --             (τ-subst (sym (+-assoc (op-time op) τ'' τ')) 
    --             (H op (τ'' + τ')) 
    --             [ Tl-∷ Hd ↦ V ]c) 
    --             [ Hd ↦ {!   !} ]c ⟩

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
            ⟨ τ , S , unbox p V M ⟩ ↝ ⟨ τ , S , M [ Hd ↦ resource-use S p V ]c ⟩

-- here i need to gather all the options of sucState
possibleStates : {τ τ' τ'' τ''' : Time} → 
                {τ≤τ' : τ ≤ τ'} → 
                {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
                {A B : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ ) → 
                SucState S S'
possibleStates APP = id-suc
possibleStates MATCH = id-suc
possibleStates SEQ-RET = id-suc
possibleStates SEQ-OP = id-suc
possibleStates DELAY = ⟨⟩-suc ≤-refl _ id-suc
possibleStates HANDLE-RET = id-suc
possibleStates BOX = ∷-suc ≤-refl _ _ id-suc
possibleStates (UNBOX p) = id-suc 
possibleStates (SEQ-FST τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = possibleStates M↝M' -- implicit args specify
possibleStates (HANDLE-STEP τ≤τ₇ τ+τ₄≡τ₇+τ₆ sucState₁ sucState₂ M↝M') = possibleStates M↝M' -- implicit args specify


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
progress {τ} {τ'} (M ; N) with progress M
... | is-value = steps ≤-refl refl SEQ-RET 
... | is-op = steps {!   !} {!   !} {!   !}
... | steps {τ} {τ'} {τ''} {τ'''} p q M↝M' = steps p {!   !} (SEQ-FST q p {!  !} M↝M')
progress {τ} {τ'} {S} (lam M · V) = steps ≤-refl refl APP
progress {τ} {τ'} (delay {τ' = τ₁} τ₂ M ) = steps (≤-stepsʳ τ₂ ≤-refl) (sym (+-assoc τ τ₂ τ₁)) DELAY
progress (match ⦉ V , W ⦊ `in M) = steps ≤-refl refl MATCH
progress (perform op V M) = is-op
progress (handle M `with H `in N) with progress M 
... | is-value = steps ≤-refl refl HANDLE-RET
... | is-op = {!   !}
... | steps p q M↝M' = steps p {!   !} (HANDLE-STEP p q {!   !} {!   !} M↝M')
progress (unbox τ≤ctx-time V M) = steps ≤-refl refl (UNBOX τ≤ctx-time)
progress (box V M) = steps ≤-refl refl BOX
progress (absurd (var V)) = ⊥-elim (Empty-not-in-ctx V)
progress (var V · N) = ⊥-elim (⇒-not-in-ctx V)
progress (match var V `in M) = ⊥-elim (⦉⦊-not-in-ctx V)
  