module Syntax.CompContext where

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

Ctx→Bctx-hom : (Γ Γ' : Ctx) → Ctx→Bctx Γ ++ₗ Ctx→Bctx Γ' ≡ Ctx→Bctx (Γ ++ᶜ Γ')
Ctx→Bctx-hom Γ [] = trans ++ₗ-identityʳ refl
Ctx→Bctx-hom Γ (Γ' ∷ x) = 
    trans (sym (++ₗ-assoc (Ctx→Bctx Γ) (Ctx→Bctx Γ') (x ∷ₗ []ₗ))) 
        (cong (_++ₗ (x ∷ₗ []ₗ)) (Ctx→Bctx-hom Γ Γ'))
Ctx→Bctx-hom Γ (Γ' ⟨ τ ⟩) =
    trans (sym (++ₗ-assoc (Ctx→Bctx Γ) (Ctx→Bctx Γ') (⟨ τ ⟩ₗ []ₗ))) 
        (cong (_++ₗ (⟨ τ ⟩ₗ []ₗ)) (Ctx→Bctx-hom Γ Γ'))

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

⋈-++ₗ-[] : (Γ Γ' : Ctx)
         → Γ ⋈ Ctx→Bctx Γ' ≡ Γ ++ᶜ Γ'
         
⋈-++ₗ-[] Γ Γ' =
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

-- Computation term context flags. They characterise whether
-- it is an arbitrary term context, an evaluation context, or
-- a state-induced context. Flags come together with a simple
-- lattice structure that is used in the def. of contexts.

data Flag : Set where
  all  : Flag
  eval : Flag
  state : Flag

data _≤ᶠ_ : Flag → Flag → Set where
  f≤ᶠf : ∀ {f : Flag} → f ≤ᶠ f
  e≤ᶠa : eval ≤ᶠ all
  s≤ᶠa : state ≤ᶠ all

infixl 31 _≤ᶠ_

≤ᶠ-trans : ∀ {f f' f''}
         → f ≤ᶠ f'
         → f' ≤ᶠ f''
         → f ≤ᶠ f''
≤ᶠ-trans f≤ᶠf q = q
≤ᶠ-trans e≤ᶠa f≤ᶠf = e≤ᶠa
≤ᶠ-trans s≤ᶠa f≤ᶠf = s≤ᶠa

_∨ᶠ_ : Flag → Flag → Flag
all   ∨ᶠ all = all
all   ∨ᶠ eval = all
all   ∨ᶠ state = all
eval  ∨ᶠ all = all
eval  ∨ᶠ eval = eval
eval  ∨ᶠ state = all
state ∨ᶠ all = all
state ∨ᶠ eval = all
state ∨ᶠ state = state

infixl 32 _∨ᶠ_

∨ᶠ-inl : ∀ {f f'}
       → f ≤ᶠ f ∨ᶠ f'
∨ᶠ-inl {all} {all} = f≤ᶠf
∨ᶠ-inl {all} {eval} = f≤ᶠf
∨ᶠ-inl {all} {state} = f≤ᶠf
∨ᶠ-inl {eval} {all} = e≤ᶠa
∨ᶠ-inl {eval} {eval} = f≤ᶠf
∨ᶠ-inl {eval} {state} = e≤ᶠa
∨ᶠ-inl {state} {all} = s≤ᶠa
∨ᶠ-inl {state} {eval} = s≤ᶠa
∨ᶠ-inl {state} {state} = f≤ᶠf

∨ᶠ-inr : ∀ {f f'}
       → f' ≤ᶠ f ∨ᶠ f'
∨ᶠ-inr {all} {all} = f≤ᶠf
∨ᶠ-inr {all} {eval} = e≤ᶠa
∨ᶠ-inr {all} {state} = s≤ᶠa
∨ᶠ-inr {eval} {all} = f≤ᶠf
∨ᶠ-inr {eval} {eval} = f≤ᶠf
∨ᶠ-inr {eval} {state} = s≤ᶠa
∨ᶠ-inr {state} {all} = f≤ᶠf
∨ᶠ-inr {state} {eval} = e≤ᶠa
∨ᶠ-inr {state} {state} = f≤ᶠf

-- Computation term contexts. The allowed cases depend on the
-- given flag.

data _⊢K[_◁_⊢_]⦂_ (Γ : Ctx) (f : Flag) : BCtx → CType → CType → Set where

    []ₖ : ∀ {A τ} 
        ---------------------------
        → Γ ⊢K[ f ◁ []ₗ ⊢ A ‼ τ ]⦂ A ‼ τ

    _ₖ[_];_ : ∀ {Δₖ Aₖ A C τₖ τ}
        → Γ ⊢K[ f ◁ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ
        → eval ≤ᶠ f
        → Γ ⟨ τₖ ⟩ ∷ Aₖ ⊢C⦂ A ‼ τ
        -----------------------------------
        → Γ ⊢K[ f ◁ Δₖ ⊢ C ]⦂ A ‼ (τₖ + τ)

    _;[_]ₖ_ : ∀ {Δₖ Aₖ A C τₖ τ} 
        → Γ ⊢C⦂ A ‼ τ
        → all ≤ᶠ f
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ f ◁ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ 
        ----------------------------------------------
        → Γ ⊢K[ f ◁ ⟨ τ ⟩ₗ A ∷ₗ Δₖ ⊢ C ]⦂ Aₖ ‼ (τ + τₖ)

    match_`in[_]ₖ_ : ∀ {Δₖ Aₖ A B C τₖ}
        → Γ ⊢V⦂ A |×| B
        → all ≤ᶠ f
        → Γ ∷ A ∷ B ⊢K[ f ◁ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ
        ----------------------------------------
        → Γ ⊢K[ f ◁ A ∷ₗ B ∷ₗ Δₖ ⊢ C ]⦂ Aₖ ‼ τₖ

    perform[_]ₖ : ∀ {Δ A C τ}
        → all ≤ᶠ f
        → (op : Op)
        → Γ ⊢V⦂ type-of-gtype (param op)
        → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢K[ f ◁ Δ ⊢ C ]⦂ A ‼ τ
        ------------------------------------------------------------------------------------
        → Γ ⊢K[ f ◁ ⟨ op-time op ⟩ₗ type-of-gtype (arity op) ∷ₗ Δ ⊢ C ]⦂ A ‼ (op-time op + τ)

    handle[_]ₖ_`with_`in
        : ∀ {Δ A B C τ τ'}
        → eval ≤ᶠ f
        → Γ ⊢K[ f ◁ Δ ⊢ C ]⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ f ◁ Δ ⊢ C ]⦂ B ‼ (τ + τ')

    handle_`with_`in[_]ₖ
        : ∀ {Δ A B C τ τ'}
        → Γ ⊢C⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → all ≤ᶠ f
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ f ◁ Δ ⊢ C ]⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ f ◁ ⟨ τ ⟩ₗ A ∷ₗ Δ ⊢ C ]⦂ B ‼ (τ + τ')

    delay[_]ₖ : ∀ {Δ A C τ'}
        → state ≤ᶠ f
        → (τ : Time)
        → Γ ⟨ τ ⟩ ⊢K[ f ◁ Δ ⊢ C ]⦂ A ‼ τ'
        -----------------------------------------
        → Γ ⊢K[ f ◁ ⟨ τ ⟩ₗ Δ ⊢ C ]⦂ A ‼ (τ + τ')
    
    unbox[_]ₖ : ∀ {Δ A C D τ}
        → all ≤ᶠ f
        → τ ≤ ctx-time Γ
        → Γ -ᶜ τ ⊢V⦂ [ τ ] A
        → Γ ∷ A  ⊢K[ f ◁ Δ ⊢ D ]⦂ C
        ----------------------------
        → Γ ⊢K[ f ◁ A ∷ₗ Δ ⊢ D ]⦂ C

    box[_]ₖ : ∀ {Δ A D C τ}
        → state ≤ᶠ f
        → Γ ⟨ τ ⟩ ⊢V⦂ A
        → Γ ∷ [ τ ] A ⊢K[ f ◁ Δ ⊢ D ]⦂ C
        ---------------------------------------
        → Γ ⊢K[ f ◁ [ τ ] A ∷ₗ Δ ⊢ D ]⦂ C

τ-substK : ∀ {Γ Δ A τ τ' C f}
        → τ ≡ τ'
        → Γ ⊢K[ f ◁ Δ ⊢ C ]⦂ A ‼ τ
        ---------------------------
        → Γ ⊢K[ f ◁ Δ ⊢ C ]⦂ A ‼ τ'

τ-substK refl K = K


-- Monotonicity if computation term contexts with respect to flags

◁-mon : ∀ {Γ Δ D C f f'}
      → f ≤ᶠ f'
      → Γ ⊢K[ f ◁ Δ ⊢ D ]⦂ C
      → Γ ⊢K[ f' ◁ Δ ⊢ D ]⦂ C
      
◁-mon {f = f} {f' = f'} p []ₖ =
  []ₖ
◁-mon {f = f} {f' = f'} p (K ₖ[ q ]; N) =
  (◁-mon p K) ₖ[ ≤ᶠ-trans q p ]; N
◁-mon {f = f} {f' = f'} p (M ;[ q ]ₖ K) =
  M ;[ ≤ᶠ-trans q p ]ₖ (◁-mon p K)
◁-mon {f = f} {f' = f'} p (match V `in[ q ]ₖ K) =
  match V `in[ ≤ᶠ-trans q p ]ₖ (◁-mon p K)
◁-mon {f = f} {f' = f'} p (perform[ q ]ₖ op V K) =
  perform[ ≤ᶠ-trans q p ]ₖ op V (◁-mon p K)
◁-mon {f = f} {f' = f'} p (handle[ q ]ₖ K `with H `in N) =
  handle[ ≤ᶠ-trans q p ]ₖ (◁-mon p K) `with H `in N
◁-mon {f = f} {f' = f'} p (handle M `with H `in[ q ]ₖ K) =
  handle M `with H `in[ ≤ᶠ-trans q p ]ₖ (◁-mon p K)
◁-mon {f = f} {f' = f'} p (delay[ q ]ₖ τ K) =
  delay[ ≤ᶠ-trans q p ]ₖ τ (◁-mon p K)
◁-mon {f = f} {f' = f'} p (unbox[ q ]ₖ r V K) =
  unbox[ ≤ᶠ-trans q p ]ₖ r V (◁-mon p K)
◁-mon {f = f} {f' = f'} p (box[ q ]ₖ V K) =
  box[ ≤ᶠ-trans q p ]ₖ V (◁-mon p K)

-- Composition of computation term contexts

_[_]ₖ : ∀ {Γ Δ Δ' D C E f f'}
     → (K : Γ ⊢K[ f ◁ Δ ⊢ D ]⦂ C)
     → (L : (Γ ⋈ Δ) ⊢K[ f' ◁ Δ' ⊢ E ]⦂ D)
     → Γ ⊢K[ f ∨ᶠ f' ◁ Δ ++ₗ Δ' ⊢ E ]⦂ C

[]ₖ [ L ]ₖ =
  ◁-mon ∨ᶠ-inr L
(K ₖ[ p ]; N) [ L ]ₖ =
  (K [ L ]ₖ) ₖ[ ≤ᶠ-trans p ∨ᶠ-inl ]; N
(M ;[ p ]ₖ K) [ L ]ₖ =
  M ;[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ)
(match V `in[ p ]ₖ K) [ L ]ₖ =
  match V `in[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ)
(perform[ p ]ₖ op V K) [ L ]ₖ =
  perform[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ op V (K [ L ]ₖ)
(handle[ p ]ₖ K `with H `in N) [ L ]ₖ =
  handle[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ) `with H `in N
(handle M `with H `in[ p ]ₖ K) [ L ]ₖ =
  handle M `with H `in[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ)
(delay[ p ]ₖ τ K) [ L ]ₖ =
  delay[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ τ (K [ L ]ₖ)
(unbox[ p ]ₖ q V K) [ L ]ₖ =
  unbox[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ q V (K [ L ]ₖ)
(box[ p ]ₖ V K) [ L ]ₖ =
  box[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ V (K [ L ]ₖ)

-- Filling a computation term context hole with a computation

_[_] : ∀ {Γ Δ D C f} 
        → (K : Γ ⊢K[ f ◁ Δ ⊢ D ]⦂ C) 
        → (M : Γ ⋈ Δ ⊢C⦂ D) 
        → Γ ⊢C⦂ C

[]ₖ [ M ] =
  M
(K ₖ[ p ]; N) [ M ] =
  (K [ M ]) ; N
(N ;[ p ]ₖ K) [ M ] =
  N ; (K [ M ])
(match V `in[ P ]ₖ K) [ M ] =
  match V `in (K [ M ])
(perform[ p ]ₖ op V K) [ M ] =
  perform op V (K [ M ])
(handle[ p ]ₖ K `with H `in N) [ M ] =
  handle (K [ M ]) `with H `in N
(handle N `with H `in[ p ]ₖ K) [ M ] =
  handle N `with H `in (K [ M ])
(delay[ p ]ₖ τ K) [ M ] =
  delay τ (K [ M ])
(unbox[ p ]ₖ q V K) [ M ] =
  unbox q V (K [ M ])
(box[ p ]ₖ V K [ M ]) =
  box V (K [ M ])

