module OperationalSemantics.PerservationTheoremCtx where

open import OperationalSemantics.StateCtx

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.Types

open import Data.Product
open import Util.Operations
open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open import Util.Time

-- record type for Configuratin that encapsulates time, state and computation

record Config (C : CType) : Set where
    constructor ⟨_,_⟩
    field
        { Δ }       : Ctx
        state       : 𝕊 Δ
        computation : toCtx state  ⊢C⦂ C

mutual 
    
    -- small-step operational semantics
    data _↝_ :  {C D : CType} → Config C → Config D → Set where

        -- usual step for function aplication
        APP :   ∀ {Δ A B τ'}
                {S : 𝕊 Δ} → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ τ'} → {V : (toCtx S) ⊢V⦂ A} →
                -------------------------------------------------------------
                ⟨ S , lam M · V ⟩ ↝ ⟨ S , M [ Hd ↦ V ]c ⟩

        -- usual step for match on pair 
        MATCH : ∀ {Δ A B C} →
                {S : 𝕊 Δ} →  
                {V : toCtx S ⊢V⦂ A } →
                {W : toCtx S ⊢V⦂ B } → 
                {M : toCtx S ∷ A ∷ B ⊢C⦂ C} → 
                -------------------------------------------------------
                ⟨ S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
                ⟨ S , (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟩

        -- step for sequencing (time and state must go on)
        SEQ-FST : ∀ {Δ Δ₁ τ₂ τ₃ τ₄} → 
                {A B : VType} → {S : 𝕊 Δ} → {S₁ : 𝕊 Δ₁} → 
                {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
                {N : ((toCtx S) ⟨ τ₂ ⟩ ∷ A) ⊢C⦂ B ‼ τ₃} → 
                {M₁ : toCtx S₁ ⊢C⦂ A ‼ τ₄} →
                (Sτ+τ₂≡Sτ₁+τ₄ : state-time S + τ₂ ≡ state-time S₁ + τ₄) →   
                (M↝M₁ : ⟨ S , M ⟩ ↝ ⟨ S₁ , M₁ ⟩) →
                --------------------------------------------------------------------
                ⟨ S , M ; N ⟩ ↝ 
                ⟨ S₁ , M₁ ;  
                    C-rename 
                        (cong-∷-ren (suc-comp-ren (step-extends-state M↝M₁) (m≡n⇒m≤n Sτ+τ₂≡Sτ₁+τ₄))) 
                        N ⟩

        -- usual step for return in sequencing
        SEQ-RET : ∀ {Δ A B τ'} → 
                {S : 𝕊 Δ} → 
                {V : (toCtx S) ⊢V⦂ A} 
                {N : ((toCtx S) ⟨ 0 ⟩ ∷ A) ⊢C⦂ B ‼ τ'} →  
                -----------------------------------------------------------------------------------
                ⟨ S , return V ; N ⟩ ↝ ⟨ S , C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟩

        -- usual performing operation in sequencing
        SEQ-OP : ∀ {Δ A B τ τ' op} →  
                {S : 𝕊 Δ} → 
                {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
                {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ} →  
                {N : toCtx S ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
                -----------------------------------------------------------------------------------
                ⟨ S , perform op V M ; N  ⟩ ↝ ⟨ S ,  τ-subst (sym (+-assoc (op-time op) τ τ'))
                             (perform op V
                                (M ;
                                 C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)) N))  ⟩

        -- delay just pass time further
        DELAY : ∀ {Δ A τ' τ''} → 
                {S : 𝕊 Δ} →
                {M : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ τ''} → 
                ---------------------------------------------------------------------
                ⟨ S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ time-pass S τ' , M ⟩

        -- usual step for handle return
        HANDLE-RET : ∀ {Δ A B τ'} →
                {S : 𝕊 Δ} → 
                {V : toCtx S ⊢V⦂ A} →
                {H : (op : Op) → (τ'' : Time) →
                    toCtx S ∷ type-of-gtype (param op)
                      ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                    ⊢C⦂ B ‼ (op-time op + τ'')} → 
                {N : toCtx S ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
                --------------------------------------------------------------------------
                ⟨ S , handle return V `with H `in N ⟩ ↝ 
                ⟨ S , (C-rename (cong-∷-ren ⟨⟩-η-ren) N) [ Hd ↦ V ]c ⟩ 

        -- step on computation in handle. time and state must go on
        HANDLE-STEP : ∀ {Δ Δ₁ A B τ₁ τ₂ τ₃} → 
                {S : 𝕊 Δ} → 
                {S₁ : 𝕊 Δ₁} → 
                {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
                {H : (op : Op) → 
                     (τ₃ : Time) →
                     toCtx S ∷ type-of-gtype (param op)
                       ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₃)
                     ⊢C⦂ B ‼ (op-time op + τ₃)} → 
                {N : toCtx S ⟨ τ₂ ⟩ ∷ A ⊢C⦂ B ‼ τ₁} → 
                {M₁ : toCtx S₁  ⊢C⦂ A ‼ τ₃ } →  
                (Sτ+τ₂≡Sτ₁+τ₃ : state-time S + τ₂ ≡ state-time S₁ + τ₃) → 
                (M↝M₁ : ⟨ S , M ⟩ ↝ ⟨ S₁ , M₁ ⟩) →
                -----------------------------------------------------------------------
                ⟨ S , handle M `with H `in N ⟩ ↝ 
                ⟨ S₁ , handle M₁ 
                            `with 
                                (λ op τ'' → 
                                    C-rename 
                                        (cong-∷-ren (cong-∷-ren (≤ₛ⇒Ren (step-extends-state M↝M₁)))) 
                                    (H op τ'')) 
                            `in (C-rename 
                                    (cong-∷-ren (suc-comp-ren (step-extends-state M↝M₁) (m≡n⇒m≤n Sτ+τ₂≡Sτ₁+τ₃))) 
                                N) ⟩

        -- operation handle where we box up result so that the resources
        -- in the result are not used before enough time has passed
        HANDLE-OP : ∀ {Δ A B τ' τ'' op} →
                {S : 𝕊 Δ} →  
                {V : toCtx S ⊢V⦂ type-of-gtype (param op)} →
                {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ''} →
                {H : (op : Op) → (τ₁ : Time) →
                    toCtx S ∷ type-of-gtype (param op)
                      ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₁)
                    ⊢C⦂ B ‼ (op-time op + τ₁)} → 
                {N : toCtx S ⟨ op-time op + τ'' ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
                --------------------------------------------------------------------------
                ⟨ S , handle perform op V M `with H `in N ⟩ ↝
                ⟨ S , box (lam (handle M 
                            `with (λ op₁ τ''' → 
                                    C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren))) 
                                (H op₁ τ''')) 
                            `in (C-rename ((cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)))
                                N))) 
                            ((H op (τ'' + τ')) [ Tl-∷ Hd ↦ V ]c) ⟩

        -- step for box: we just extend our state with new resource
        BOX :   ∀ {Δ A B τ' τ''} → {S : 𝕊 Δ} → 
                {V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A} →  
                {M : toCtx S ∷ [ τ' ] A ⊢C⦂ B ‼ τ''} →
                -------------------------------------------------------
                ⟨ S , (box V M) ⟩ ↝ ⟨ extend-state S (V-rename (cong-⟨⟩-ren (eq-ren (sym (Γ≡toCtxS S)))) V) , M ⟩

        -- step for unbox: we just substitute in M with unboxed resource (finding the right one is tricky)
        UNBOX : ∀ {Δ A C τ'} → {S : 𝕊 Δ} → 
                (p : τ' ≤ ctx-time (toCtx S)) → 
                {V : (toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)} →
                {M : toCtx S ∷ A ⊢C⦂ C } → 
                ---------------------------------------------------------------------------------------------
                let Σ[τ''∈Time][τ+τ'≤τ''×A∈[τ'']Γ] = (push-time-further p (proj₂ (var-in-ctx V))) in
                let all-time-smaller = m+n≤o⇒m≤o τ' (proj₁ (proj₂ Σ[τ''∈Time][τ+τ'≤τ''×A∈[τ'']Γ])) in
                let time-travel-to-past-smaller-than-ctx-time = τ-≤-substᵣ 
                                (sym (ctx-time≡state-time S))
                                (from-head-time-positive (proj₂ (proj₂ Σ[τ''∈Time][τ+τ'≤τ''×A∈[τ'']Γ]))) in
                ⟨ S , unbox p V M ⟩ ↝ 
                ⟨ S , 
                    M [ Hd ↦ 
                        resource-pass-to-ctx 
                            S 
                            all-time-smaller
                            time-travel-to-past-smaller-than-ctx-time
                            (resource-lookup S (proj₂ (proj₂ Σ[τ''∈Time][τ+τ'≤τ''×A∈[τ'']Γ]))) ]c ⟩ 
            
    -- Theorem that step only extends state
    step-extends-state : ∀ {Δ Δ' τ'' τ'''} → 
                {S : 𝕊 Δ} → {S' : 𝕊 Δ'} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ ) → 
                S ≤ₛ S'
    step-extends-state APP = id-suc
    step-extends-state MATCH = id-suc
    step-extends-state SEQ-RET = id-suc
    step-extends-state SEQ-OP = id-suc
    step-extends-state HANDLE-RET = id-suc
    step-extends-state (UNBOX p) = id-suc 
    step-extends-state HANDLE-OP = id-suc
    step-extends-state DELAY = ⟨⟩-suc _ id-suc
    step-extends-state BOX = ∷-suc _ id-suc
    step-extends-state (SEQ-FST {M = M} {M₁ = M'} τ+τ₂≡τ₁+τ₄ M↝M') = step-extends-state  M↝M'
    step-extends-state (HANDLE-STEP {M = M} {M₁ = M'} τ+τ₄≡τ₇+τ₆ M↝M') = step-extends-state M↝M'


-- perservation theorem

perservation-theorem : ∀ {Δ Δ' A B τ'' τ'''}
                → {S : 𝕊 Δ}
                → {S' : 𝕊 Δ'}
                → {M : toCtx S ⊢C⦂ A ‼ τ''}
                → {M' : toCtx S' ⊢C⦂ B ‼ τ'''}
                → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                → A ≡ B × state-time S + τ'' ≡ state-time S' + τ'''
perservation-theorem APP = refl , refl
perservation-theorem MATCH = refl , refl
perservation-theorem {S = S} {S' = S'} (SEQ-FST {τ₂ = τ₂} {τ₃} {τ₄} τ+τ₂≡τ₁+τ₄ M↝M') = 
    refl , τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] (state-time S) (state-time S') τ₂ τ₃ τ₄ τ+τ₂≡τ₁+τ₄
perservation-theorem SEQ-RET = refl , refl
perservation-theorem SEQ-OP = refl , refl
perservation-theorem {τ''' = τ'''} {S = S} (DELAY {τ' = τ'}) = 
    refl , sym (+-assoc (state-time S) τ' τ''')
perservation-theorem HANDLE-RET = refl , refl
perservation-theorem {S = S} {S' = S'} (HANDLE-STEP {τ₁ = τ₁} {τ₂} {τ₃} τ+τ₂≡τ₄+τ₃ M↝M') = 
    refl , τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] (state-time S) (state-time S') τ₂ τ₁ τ₃ τ+τ₂≡τ₄+τ₃
perservation-theorem {S = S} (HANDLE-OP {τ' = τ'} {τ'' = τ''} {op = op}) = 
    refl , cong ((state-time S) +_) (+-assoc (op-time op) τ'' τ')
perservation-theorem BOX = refl , refl
perservation-theorem (UNBOX p) = refl , refl 
