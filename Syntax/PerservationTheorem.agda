module Syntax.PerservationTheorem where

open import Syntax.State
open import Util.Time
open import Util.Properties
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Util.Operations
open import Syntax.Substitutions
open import Syntax.Renamings
open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

-- record type for Configuratin that encapsulates time, state and computation

record Config (C : CType) : Set where
    constructor ⟨_,_,_⟩
    field
        τ : Time
        state : 𝕊 τ
        computation : toCtx state  ⊢C⦂ C

-- small-step operational semantics

data _↝_ :  {C D : CType} → Config C → Config D → Set where
    
    -- usual step for function aplication
    APP :   {A B : VType} {τ τ' : Time} 
            {S : 𝕊 τ} → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ τ'} → {V : (toCtx S) ⊢V⦂ A} →
            -------------------------------------------------------------
            ⟨ τ , S , lam M · V ⟩ ↝ ⟨ τ , S , M [ Hd ↦ V ]c ⟩

    -- usual step for match on pair 
    MATCH : {τ : Time} {S : 𝕊 τ} {A B : VType} {C : CType} → 
            {V : toCtx S ⊢V⦂ A } →
            {W : toCtx S ⊢V⦂ B } → 
            {M : toCtx S ∷ A ∷ B ⊢C⦂ C} → 
            -------------------------------------------------------
            ⟨ τ , S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
            ⟨ τ , S , (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟩
    
    -- step for sequencing (time and state must go on)
    SEQ-FST : {τ τ₁ τ₂ τ₃ τ₄ : Time} → 
            {A B : VType} → {S : 𝕊 τ} → {S₁ : 𝕊 τ₁} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
            {N : ((toCtx S) ⟨ τ₂ ⟩ ∷ A) ⊢C⦂ B ‼ τ₃} → 
            {M₁ : toCtx S₁ ⊢C⦂ A ‼ τ₄} →
            (τ+τ₂≡τ₁+τ₄ : τ + τ₂ ≡ τ₁ + τ₄) →  
            (τ≤τ₁ : τ ≤ τ₁) → 
            (sucState : SucState S S₁) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ₁ , S₁ , M₁ ⟩ →
            --------------------------------------------------------------------
            ⟨ τ , S , M ; N ⟩ ↝ 
            ⟨ τ₁ , S₁ , M₁ ; (C-rename (cong-∷-ren (suc-comp-ren τ≤τ₁ sucState (C-rename wk-⟨⟩-ren M) (m≡n⇒m≤n τ+τ₂≡τ₁+τ₄))) N) ⟩  

    -- usual step for return in sequencing
    SEQ-RET : {τ τ' : Time} → 
            {A B : VType} → {S : 𝕊 τ} → 
            {V : (toCtx S) ⊢V⦂ A} 
            {N : ((toCtx S) ⟨ 0 ⟩ ∷ A) ⊢C⦂ B ‼ τ'} →  
            -----------------------------------------------------------------------------------
            ⟨ τ , S , return V ; N ⟩ ↝ ⟨ τ , S , C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟩
    
    -- usual performing operation in sequencing
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
                             C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren))
                             N))  ⟩
    
    -- delay just pass time further
    DELAY : {τ τ' τ'' : Time} → 
            {S : 𝕊 τ} →
            {A : VType} →  
            {M : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ τ''} → 
            ---------------------------------------------------------------------
            ⟨ τ , S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ τ + τ' , time-pass S τ' , M ⟩

    -- usual step for handle return
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
    
    -- step on computation in handle. time and state must go on
    HANDLE-STEP : {A B : VType} →
            {τ τ₁ τ₂ τ₃ τ₄ : Time} → 
            {S : 𝕊 τ} → 
            {S₁ : 𝕊 τ₄} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
            {H : (op : Op) → 
                 (τ₃ : Time) →
                 toCtx S ∷ type-of-gtype (param op)
                   ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₃)
                 ⊢C⦂ B ‼ (op-time op + τ₃)} → 
            {N : toCtx S ⟨ τ₂ ⟩ ∷ A ⊢C⦂ B ‼ τ₁} → 
            {M₁ : toCtx S₁  ⊢C⦂ A ‼ τ₃ } →  
            (τ≤τ₄ : τ ≤ τ₄) → 
            (τ+τ₂≡τ₄+τ₃ : τ + τ₂ ≡ τ₄ + τ₃) → 
            (sucState : SucState S S₁) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ₄ , S₁ , M₁ ⟩ → 
            -----------------------------------------------------------------------
            ⟨ τ , S , handle M `with H `in N ⟩ ↝ 
            ⟨ τ₄ , S₁ , handle M₁ 
                        `with 
                            (λ op τ'' → 
                                C-rename 
                                    (cong-∷-ren (cong-∷-ren (SucState⇒Ren τ≤τ₄ sucState))) 
                                (H op τ'')) 
                        `in (C-rename 
                                (cong-∷-ren (suc-comp-ren τ≤τ₄ sucState (C-rename wk-⟨⟩-ren M) (m≡n⇒m≤n τ+τ₂≡τ₄+τ₃))) 
                            N) ⟩

    -- operaion handle where we box up result so that time in the rest of the 
    -- program doesn't break
    HANDLE-OP : {τ τ' τ'' : Time} →
            {S : 𝕊 τ} → 
            {op : Op} → 
            {A B : VType} → 
            {V : toCtx S ⊢V⦂ type-of-gtype (param op)} →
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ''} →
            {H : (op : Op) → (τ₁ : Time) →
                toCtx S ∷ type-of-gtype (param op)
                  ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₁)
                ⊢C⦂ B ‼ (op-time op + τ₁)} → 
            {N : toCtx S ⟨ op-time op + τ'' ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
            --------------------------------------------------------------------------
            ⟨ τ , S , handle perform op V M `with H `in N ⟩ ↝
            ⟨ τ , S , 
            box (lam (handle M 
                    `with (λ op₁ τ''' → 
                            C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren))) 
                        (H op₁ τ''')) 
                    `in (C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)) 
                        N))) 
                ((H op (τ'' + τ')) [ Tl-∷ Hd ↦ V ]c) ⟩

    -- step for box: we just extend our state with new resource
    BOX :   {τ τ' τ'' : Time} → {S : 𝕊 τ} → {A B : VType} → 
            {V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A} →  
            {M : toCtx S ∷ [ τ' ] A ⊢C⦂ B ‼ τ''} →
            -------------------------------------------------------
            ⟨ τ , S , (box V M) ⟩ ↝ ⟨ τ , extend-state S τ' V , M ⟩

    -- step for unbox: we just substitute in M with unboxed resource (finding the right one is tricky)
    UNBOX : {τ τ' : Time} → {S : 𝕊 τ} →  {A : VType} → {C : CType} → 
            (p : τ' ≤ ctx-time (toCtx S)) → 
            {V : (toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)} →
            {M : toCtx S ∷ A ⊢C⦂ C } → 
            ---------------------------------------------------------------------------------------------
            ⟨ τ , S , unbox p V M ⟩ ↝ 
            ⟨ τ , S , 
            M [ Hd ↦ 
                resource-pass-to-ctx 
                    S 
                    (m+n≤o⇒m≤o 
                        τ' 
                        (proj₁ (proj₂ (
                            push-time-further 
                                p 
                                (proj₂ (var-in-ctx V))
                                    )
                                )
                        )
                    ) 
                    (τ-≤-substᵣ 
                        (sym (ctx-timeSτ≡τ S))
                        (from-head-time-positive (proj₂ (proj₂ (push-time-further p (proj₂ (var-in-ctx V))))))
                    )
                    (resource-use 
                        S 
                        (proj₂ (proj₂ (
                            push-time-further p (proj₂ (var-in-ctx V)))))) ]c ⟩ 

-- perservation theorem

perseration-theorem : ∀ {A B τ τ' τ'' τ'''}
                → {S : 𝕊 τ}
                → {S' : 𝕊 τ'}
                → {M : toCtx S ⊢C⦂ A ‼ τ''}
                → {M' : toCtx S' ⊢C⦂ B ‼ τ'''}
                → ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩
                → A ≡ B
perseration-theorem APP = refl
perseration-theorem MATCH = refl
perseration-theorem (SEQ-FST τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = refl
perseration-theorem SEQ-RET = refl
perseration-theorem SEQ-OP = refl
perseration-theorem DELAY = refl
perseration-theorem HANDLE-RET = refl
perseration-theorem (HANDLE-STEP τ≤τ₄ τ+τ₂≡τ₄+τ₃ sucState M↝M') = refl
perseration-theorem HANDLE-OP = refl
perseration-theorem BOX = refl
perseration-theorem (UNBOX p) = refl