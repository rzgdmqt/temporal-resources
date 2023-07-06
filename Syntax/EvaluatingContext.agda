module Syntax.EvaluatingContext where

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Util.Operations
open import Util.Time

-- Context with appending on the left end
data BCtx : Set where
  []ₗ   : BCtx               
  _∷ₗ_  : VType → BCtx → BCtx 
  ⟨_⟩ₗ_ : Time → BCtx → BCtx  

infixl 32 _∷ₗ_
infix  31 ⟨_⟩ₗ_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ []ₗ = Γ
Γ ⋈ (x ∷ₗ Δ) = ((Γ ∷ x)) ⋈ Δ
Γ ⋈ (⟨ τ ⟩ₗ Δ) = (Γ ⟨ τ ⟩) ⋈ Δ 

BCtx→Ctx : BCtx → Ctx 
BCtx→Ctx []ₗ = []
BCtx→Ctx (x ∷ₗ Δ) = ([] ∷ x) ++ᶜ BCtx→Ctx Δ
BCtx→Ctx (⟨ τ ⟩ₗ Δ) = ([] ⟨ τ ⟩) ++ᶜ BCtx→Ctx Δ

bctx-time : (Δ : BCtx) → Time
bctx-time []ₗ = 0
bctx-time (X ∷ₗ Δ) = bctx-time Δ
bctx-time (⟨ τ ⟩ₗ Δ) = τ + (bctx-time Δ)

infixl 30 _⋈_ 

-- program with typed hole in it
data _⊢K[_]⦂_ (Γ : Ctx) : BCtx → CType → Set where

    []ₖ : ∀ {A τ} 
        -------------------
        → Γ ⊢K[ []ₗ ]⦂ A ‼ τ
        
    _ₖ;_ : ∀ {Δₖ Aₖ A τₖ τ} 
        → Γ ⊢K[ Δₖ ]⦂ Aₖ ‼ τₖ 
        → Γ ⟨ τₖ ⟩ ∷ Aₖ ⊢C⦂ A ‼ τ
        -------------------------
        → Γ ⊢K[ Δₖ ]⦂ A ‼ (τₖ + τ)

    _;ₖ_ : ∀ {Δₖ Aₖ A τₖ τ} 
        → Γ ⊢C⦂ A ‼ τ
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ Δₖ ]⦂ Aₖ ‼ τₖ 
        ------------------------------------
        → Γ ⊢K[ ⟨ τ ⟩ₗ A ∷ₗ Δₖ ]⦂ Aₖ ‼ (τ + τₖ)
    
    performₖ : ∀ {Δ A τ op}
        → Γ ⊢V⦂ type-of-gtype (param op)
        → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢K[ Δ ]⦂ A ‼ τ
        ---------------------------------------------------------------------------
        → Γ ⊢K[ ⟨ op-time op ⟩ₗ type-of-gtype (arity op) ∷ₗ Δ ]⦂ A ‼ (op-time op + τ)

    handleₖ_`with_`in
        : ∀ {Δ A B τ τ'}
        → Γ ⊢K[ Δ ]⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ Δ ]⦂ B ‼ (τ + τ')
    
    handle_`with_`inₖ
        : ∀ {Δ A B τ τ'}
        → Γ ⊢C⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ Δ ]⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ ⟨ τ ⟩ₗ A ∷ₗ Δ ]⦂ B ‼ (τ + τ')
    
    delayₖ : ∀ {Δ A τ'}
        → (τ : Time)
        → Γ ⟨ τ ⟩ ⊢K[ Δ ]⦂ A ‼ τ'
        -------------------------------
        → Γ ⊢K[ ⟨ τ ⟩ₗ Δ ]⦂ A ‼ (τ + τ')
    
    unboxₖ : ∀ {Δ A C τ}
        → τ ≤ ctx-time Γ
        → Γ -ᶜ τ ⊢V⦂ [ τ ] A
        → Γ ∷ A  ⊢K[ Δ ]⦂ C
        --------------------
        → Γ ⊢K[ A ∷ₗ Δ ]⦂ C

    boxₖ : ∀ {Δ A B τ τ'}
        → Γ ⟨ τ ⟩ ⊢V⦂ A
        → Γ ∷ [ τ ] A ⊢K[ Δ ]⦂ B ‼ τ'
        ----------------------------
        → Γ ⊢K[ [ τ ] A ∷ₗ Δ ]⦂ B ‼ τ'
        

-- hole type
holeTy : ∀ {Γ Δ C} → Γ ⊢K[ Δ ]⦂ C → CType
holeTy {_} {_} {C} []ₖ = C
holeTy (K ₖ; M) = holeTy K
holeTy (M ;ₖ K) = holeTy K
holeTy (performₖ op K) = holeTy K
holeTy (handleₖ K `with H `in M) = holeTy K
holeTy (handle M `with H `inₖ K) = holeTy K
holeTy (delayₖ τ K) = holeTy K
holeTy (unboxₖ τ≤ctxTimeΓ V K) = holeTy K
holeTy (boxₖ V K) = holeTy K


-- hole filling function
_ₖ[_] : ∀ {Γ Δ C} 
        → (K : Γ ⊢K[ Δ ]⦂ C) 
        → (M : Γ ⋈ Δ ⊢C⦂ (holeTy K)) 
        → Γ ⊢C⦂ C
[]ₖ ₖ[ M ] = M
(K ₖ; N) ₖ[ M ] = (K ₖ[ M ]) ; N
(N ;ₖ K) ₖ[ M ] = N ; (K ₖ[ M ])
performₖ {op = op} V K ₖ[ M ] = perform op V (K ₖ[ M ])
handleₖ K `with H `in N ₖ[ M ] = handle K ₖ[ M ] `with H `in N
handle N `with H `inₖ K ₖ[ M ] = handle N `with H `in (K ₖ[ M ])
delayₖ τ K ₖ[ M ] = delay τ (K ₖ[ M ])
unboxₖ τ≤ctxTimeΓ V K ₖ[ M ] = unbox τ≤ctxTimeΓ V (K ₖ[ M ])
boxₖ V K ₖ[ M ] = box V (K ₖ[ M ])


    -- Gamma |-[Gamma' ; D] K : C


    -- Gamma |-[ Gamma' ; C ] [] : C


    -- Gamma |-[Gamma' ; D] K : C   &&   Gamma,Gamma' |- M : D    ==>    Gamma |- K[M] : C



    -- box V as r in (op W y.N) = op W y. (box V as r in N)
   