module EquationalTheory.CompContext where

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Types

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Context with appending on the left end

data BCtx : Set where
  []ₗ   : BCtx               
  _∷ₗ_  : VType → BCtx → BCtx 
  ⟨_⟩ₗ_ : Time → BCtx → BCtx  

infixr 32 _∷ₗ_
infix  31 ⟨_⟩ₗ_

-- Operation that merges context and binding context, by
-- transfering resources and time passages one by one from
-- binding context to regular context

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ []ₗ = Γ
Γ ⋈ (A ∷ₗ Δ) = ((Γ ∷ A)) ⋈ Δ
Γ ⋈ (⟨ τ ⟩ₗ Δ) = (Γ ⟨ τ ⟩) ⋈ Δ

infixl 30 _⋈_

-- function transforming binding context to regular context
-- one might use simpler expression BCtx→Ctx Δ = [] ⋈ Δ, but
-- we have powerfull lemmas for _ ++ᶜ_ that are more of a use
-- along the following definition

BCtx→Ctx : BCtx → Ctx 
BCtx→Ctx []ₗ = []
BCtx→Ctx (A ∷ₗ Δ) = ([] ∷ A) ++ᶜ BCtx→Ctx Δ
BCtx→Ctx (⟨ τ ⟩ₗ Δ) = ([] ⟨ τ ⟩) ++ᶜ BCtx→Ctx Δ

-- concatenating binding contexts

_++ₗ_ : BCtx → BCtx → BCtx
[]ₗ ++ₗ Δ' = Δ'
(A ∷ₗ Δ) ++ₗ Δ' = A ∷ₗ (Δ ++ₗ Δ')
(⟨ τ ⟩ₗ Δ) ++ₗ Δ' = ⟨ τ ⟩ₗ (Δ ++ₗ Δ')

infixl 6 _++ₗ_

-- associativity of concatenating binding contexts

++ₗ-assoc : (Δ Δ' Δ'' : BCtx)
          → Δ ++ₗ Δ' ++ₗ Δ'' ≡ Δ ++ₗ (Δ' ++ₗ Δ'')
          
++ₗ-assoc []ₗ Δ' Δ'' = refl
++ₗ-assoc (A ∷ₗ Δ) Δ' Δ'' = cong (A ∷ₗ_) (++ₗ-assoc Δ Δ' Δ'')
++ₗ-assoc (⟨ τ ⟩ₗ Δ) Δ' Δ'' = cong (⟨ τ ⟩ₗ_) (++ₗ-assoc Δ Δ' Δ'')

-- unitality of concatenating binding contexts

++ₗ-identityˡ : ∀ {Δ}
              → []ₗ ++ₗ Δ ≡ Δ
              
++ₗ-identityˡ = refl

++ₗ-identityʳ : ∀ {Δ}
              → Δ ++ₗ []ₗ ≡ Δ
              
++ₗ-identityʳ {[]ₗ} = refl
++ₗ-identityʳ {A ∷ₗ Δ} = cong (A ∷ₗ_) (++ₗ-identityʳ {Δ})
++ₗ-identityʳ {⟨ τ ⟩ₗ Δ} = cong (⟨ τ ⟩ₗ_) (++ₗ-identityʳ {Δ})

-- transforming context to binding context

Ctx→Bctx : Ctx → BCtx
Ctx→Bctx [] = []ₗ
Ctx→Bctx (Γ ∷ A) = Ctx→Bctx Γ ++ₗ (A ∷ₗ []ₗ)
Ctx→Bctx (Γ ⟨ τ ⟩) = (Ctx→Bctx Γ) ++ₗ (⟨ τ ⟩ₗ []ₗ)

-- Relating ⋈ and Ctx→Bctx

⋈-++ₗ : (Γ Γ' : Ctx)
      → (Δ : BCtx)
      → Γ ⋈ (Ctx→Bctx Γ' ++ₗ Δ) ≡ (Γ ++ᶜ Γ') ⋈ Δ

⋈-++ₗ Γ [] Δ =
  refl
⋈-++ₗ Γ (Γ' ∷ A) Δ =
  trans
    (cong (Γ ⋈_) (++ₗ-assoc (Ctx→Bctx Γ') (A ∷ₗ []ₗ) Δ))
    (⋈-++ₗ Γ Γ' (A ∷ₗ Δ))
⋈-++ₗ Γ (Γ' ⟨ τ ⟩) Δ =
  trans
    (cong (Γ ⋈_) (++ₗ-assoc (Ctx→Bctx Γ') (⟨ τ ⟩ₗ []ₗ) Δ)) 
    (⋈-++ₗ Γ Γ' (⟨ τ ⟩ₗ Δ))

⋈-BCtx→Ctx : (Γ Γ' : Ctx)
           → Γ ⋈ Ctx→Bctx Γ' ≡ Γ ++ᶜ Γ'

⋈-BCtx→Ctx Γ Γ' =
  trans
    (cong (Γ ⋈_) (sym (++ₗ-identityʳ {Ctx→Bctx Γ'})))
    (⋈-++ₗ Γ Γ' []ₗ)

-- binding context time. Just for convenience. We could
-- use: ctx-time (BCtx→Ctx Δ)

bctx-time : (Δ : BCtx) → Time
bctx-time []ₗ = 0
bctx-time (A ∷ₗ Δ) = bctx-time Δ
bctx-time (⟨ τ ⟩ₗ Δ) = τ + (bctx-time Δ)

-- Linearity of bctx

bctx-time-aditive : (Δ Δ' : BCtx)
                 → bctx-time (Δ ++ₗ Δ') ≡ bctx-time Δ + bctx-time Δ'

bctx-time-aditive []ₗ Δ' =
  refl
bctx-time-aditive (A ∷ₗ Δ) Δ' =
  bctx-time-aditive Δ Δ'
bctx-time-aditive (⟨ τ ⟩ₗ Δ) Δ' =
  trans
    (cong (τ +_) (bctx-time-aditive Δ Δ'))
    (sym (+-assoc τ (bctx-time Δ) (bctx-time Δ')))

-- Relating bctx-time to ctx-time

bctx-time-ctx-time : (Γ : Ctx)
                   → bctx-time (Ctx→Bctx Γ) ≡ ctx-time Γ

bctx-time-ctx-time [] =
  refl
bctx-time-ctx-time (Γ ∷ A) =
  trans 
    (bctx-time-aditive (Ctx→Bctx Γ) (A ∷ₗ []ₗ))
    (trans
      (+-identityʳ _)
      (bctx-time-ctx-time Γ))
bctx-time-ctx-time (Γ ⟨ τ ⟩) =
  trans
    (bctx-time-aditive (Ctx→Bctx Γ) (⟨ τ ⟩ₗ []ₗ))
    (trans
      (cong (bctx-time (Ctx→Bctx Γ) +_) (+-identityʳ _))
      (cong (_+ τ) (bctx-time-ctx-time Γ)))

ctx-time-bctx-time : (Δ : BCtx)
                   → ctx-time (BCtx→Ctx Δ) ≡ bctx-time Δ
ctx-time-bctx-time []ₗ = 
  refl
ctx-time-bctx-time (A ∷ₗ Δ) = 
  trans 
    (ctx-time-++ᶜ ([] ∷ A) (BCtx→Ctx Δ)) 
    (ctx-time-bctx-time Δ)
ctx-time-bctx-time (⟨ τ ⟩ₗ Δ) = 
  trans 
    (ctx-time-++ᶜ ([] ⟨ τ ⟩) (BCtx→Ctx Δ)) 
    (cong (τ +_) (ctx-time-bctx-time Δ))

-- program with typed hole in it - basicly just computations
-- where in place of computation we can use hole 𝕂
data _⊢K[_⊢_]⦂_ (Γ : Ctx) : BCtx → CType → CType → Set where

    []ₖ : ∀ {A τ} 
        ---------------------------
        → Γ ⊢K[ []ₗ ⊢ A ‼ τ ]⦂ A ‼ τ
        
    _ₖ;_ : ∀ {Δₖ Aₖ A C τₖ τ} 
        → Γ ⊢K[ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ 
        → Γ ⟨ τₖ ⟩ ∷ Aₖ ⊢C⦂ A ‼ τ
        -----------------------------------
        → Γ ⊢K[ Δₖ ⊢ C ]⦂ A ‼ (τₖ + τ)

    _;ₖ_ : ∀ {Δₖ Aₖ A C τₖ τ} 
        → Γ ⊢C⦂ A ‼ τ
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ 
        ----------------------------------------------
        → Γ ⊢K[ ⟨ τ ⟩ₗ A ∷ₗ Δₖ ⊢ C ]⦂ Aₖ ‼ (τ + τₖ)
    
    match_`inₖ_ : ∀ {Δₖ Aₖ A B C τₖ}
        → Γ ⊢V⦂ A |×| B
        → Γ ∷ A ∷ B ⊢K[ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ
        ----------------------------------------
        → Γ ⊢K[ A ∷ₗ B ∷ₗ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ

    performₖ : ∀ {Δ A C τ op}
        → Γ ⊢V⦂ type-of-gtype (param op)
        → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢K[ Δ ⊢ C ]⦂ A ‼ τ
        ------------------------------------------------------------------------------------
        → Γ ⊢K[ ⟨ op-time op ⟩ₗ type-of-gtype (arity op) ∷ₗ Δ ⊢ C ]⦂ A ‼ (op-time op + τ)

    handleₖ_`with_`in
        : ∀ {Δ A B C τ τ'}
        → Γ ⊢K[ Δ ⊢ C ]⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ Δ ⊢ C ]⦂ B ‼ (τ + τ')
    
    handle_`with_`inₖ
        : ∀ {Δ A B C τ τ'}
        → Γ ⊢C⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ Δ ⊢ C ]⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ ⟨ τ ⟩ₗ A ∷ₗ Δ ⊢ C ]⦂ B ‼ (τ + τ')
    
    delayₖ : ∀ {Δ A C τ'}
        → (τ : Time)
        → Γ ⟨ τ ⟩ ⊢K[ Δ ⊢ C ]⦂ A ‼ τ'
        -----------------------------------------
        → Γ ⊢K[ ⟨ τ ⟩ₗ Δ ⊢ C ]⦂ A ‼ (τ + τ')
    
    unboxₖ : ∀ {Δ A C D τ}
        → τ ≤ ctx-time Γ
        → Γ -ᶜ τ ⊢V⦂ [ τ ] A
        → Γ ∷ A  ⊢K[ Δ ⊢ D ]⦂ C
        ----------------------------
        → Γ ⊢K[ A ∷ₗ Δ ⊢ D ]⦂ C

    boxₖ : ∀ {Δ A B C τ τ'}
        → Γ ⟨ τ ⟩ ⊢V⦂ A
        → Γ ∷ [ τ ] A ⊢K[ Δ ⊢ C ]⦂ B ‼ τ'
        ---------------------------------------
        → Γ ⊢K[ [ τ ] A ∷ₗ Δ ⊢ C ]⦂ B ‼ τ'

-- hole filling function
_ₖ[_] : ∀ {Γ Δ D C} 
        → (K : Γ ⊢K[ Δ ⊢ D ]⦂ C) 
        → (M : Γ ⋈ Δ ⊢C⦂ D) 
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
(match V `inₖ K) ₖ[ M ] = match V `in (K ₖ[ M ])
