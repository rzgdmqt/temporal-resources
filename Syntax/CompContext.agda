module Syntax.CompContext where

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Types

open import Util.Equality
open import Util.Operations
open import Util.Time

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

data _⊢K[_]⦂_ (Γ : Ctx) (f : Flag) : CType → Set where

    []ₖ : ∀ {C} 
        ------------------
        → Γ ⊢K[ f ]⦂ C

    _ₖ[_];_ : ∀ {Aₖ A τₖ τ}
        → Γ ⊢K[ f ]⦂ Aₖ ‼ τₖ
        → eval ≤ᶠ f
        → Γ ⟨ τₖ ⟩ ∷ Aₖ ⊢C⦂ A ‼ τ
        -----------------------------
        → Γ ⊢K[ f ]⦂ A ‼ (τₖ + τ)

    _;[_]ₖ_ : ∀ {Aₖ A τₖ τ} 
        → Γ ⊢C⦂ A ‼ τ
        → all ≤ᶠ f
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ f ]⦂ Aₖ ‼ τₖ 
        ----------------------------------
        → Γ ⊢K[ f ]⦂ Aₖ ‼ (τ + τₖ)

    match_`in[_]ₖ_ : ∀ {Aₖ A B τₖ}
        → Γ ⊢V⦂ A |×| B
        → all ≤ᶠ f
        → Γ ∷ A ∷ B ⊢K[ f ]⦂ Aₖ ‼ τₖ
        -------------------------------
        → Γ ⊢K[ f ]⦂ Aₖ ‼ τₖ

    perform[_]ₖ : ∀ {A τ}
        → all ≤ᶠ f
        → (op : Op)
        → Γ ⊢V⦂ type-of-gtype (param op)
        → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢K[ f ]⦂ A ‼ τ
        ----------------------------------------------------------------
        → Γ ⊢K[ f ]⦂ A ‼ (op-time op + τ)

    handle[_]ₖ_`with_`in
        : ∀ {A B τ τ'}
        → eval ≤ᶠ f
        → Γ ⊢K[ f ]⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ f ]⦂ B ‼ (τ + τ')

    handle_`with_`in[_]ₖ
        : ∀ {A B τ τ'}
        → Γ ⊢C⦂ A ‼ τ
        → ((op : Op) → (τ'' : Time) →
             Γ ∷ type-of-gtype (param op)
               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
             ⊢C⦂ B ‼ (op-time op + τ''))
        → all ≤ᶠ f
        → Γ ⟨ τ ⟩ ∷ A ⊢K[ f ]⦂ B ‼ τ'
        ------------------------------------------------------------
        → Γ ⊢K[ f ]⦂ B ‼ (τ + τ')

    delay[_]ₖ : ∀ {A τ'}
        → state ≤ᶠ f
        → (τ : Time)
        → Γ ⟨ τ ⟩ ⊢K[ f ]⦂ A ‼ τ'
        -----------------------------
        → Γ ⊢K[ f ]⦂ A ‼ (τ + τ')

    unbox[_]ₖ : ∀ {A C τ}
        → all ≤ᶠ f
        → τ ≤ ctx-time Γ
        → Γ -ᶜ τ ⊢V⦂ [ τ ] A
        → Γ ∷ A  ⊢K[ f ]⦂ C
        -----------------------
        → Γ ⊢K[ f ]⦂ C
    
    box[_]ₖ : ∀ {A C τ}
        → state ≤ᶠ f
        → Γ ⟨ τ ⟩ ⊢V⦂ A
        → Γ ∷ [ τ ] A ⊢K[ f ]⦂ C
        ----------------------------
        → Γ ⊢K[ f ]⦂ C

-- Type of the hole in a computation term context

hole-ty : ∀ {Γ f C} → Γ ⊢K[ f ]⦂ C → CType

hole-ty ([]ₖ {C = C}) = C
hole-ty (K ₖ[ p ]; N) = hole-ty K
hole-ty (M ;[ p ]ₖ K) = hole-ty K
hole-ty (match V `in[ p ]ₖ K) = hole-ty K
hole-ty (perform[ p ]ₖ op V K) = hole-ty K
hole-ty (handle[ p ]ₖ K `with H `in N) = hole-ty K
hole-ty (handle M `with H `in[ p ]ₖ K) = hole-ty K
hole-ty (delay[ p ]ₖ τ K) = hole-ty K
hole-ty (unbox[ p ]ₖ q V K) = hole-ty K
hole-ty (box[ p ]ₖ V K) = hole-ty K

-- Contexts of the hole in a computation term context
-- (the relative version, against arbitrary ctx Γ')
-- (turns a computation term contexts into a Hughes list)

rel-hole-ctx : ∀ {Γ f C} → Γ ⊢K[ f ]⦂ C → Ctx → Ctx

rel-hole-ctx []ₖ Γ' =
  Γ'
rel-hole-ctx (K ₖ[ p ]; N) Γ' =
  rel-hole-ctx K Γ'
rel-hole-ctx (_;[_]ₖ_ {A = A} {τ = τ} M p K) Γ' =
  rel-hole-ctx K (Γ' ⟨ τ ⟩ ∷ A)
rel-hole-ctx (match_`in[_]ₖ_ {A = A} {B = B} V p K) Γ' =
  rel-hole-ctx K (Γ' ∷ A ∷ B)
rel-hole-ctx (perform[_]ₖ p op V K) Γ' =
  rel-hole-ctx K (Γ' ⟨ op-time op ⟩ ∷ type-of-gtype (arity op))
rel-hole-ctx (handle[ p ]ₖ K `with H `in N) Γ' =
  rel-hole-ctx K Γ'
rel-hole-ctx (handle_`with_`in[_]ₖ {A = A} {τ = τ} M H p K) Γ' =
  rel-hole-ctx K (Γ' ⟨ τ ⟩ ∷ A)
rel-hole-ctx (delay[ p ]ₖ τ K) Γ' =
  rel-hole-ctx K (Γ' ⟨ τ ⟩)
rel-hole-ctx (unbox[_]ₖ {A = A} p q V K) Γ' =
  rel-hole-ctx K (Γ' ∷ A)
rel-hole-ctx (box[_]ₖ {A = A} {τ = τ} p V K) Γ' =
  rel-hole-ctx K (Γ' ∷ [ τ ] A)

-- Contexts of the hole in a computation term context
-- (the relative version, with only the vars bound in K)

hole-ctx : ∀ {Γ f C} → Γ ⊢K[ f ]⦂ C → Ctx
hole-ctx K = rel-hole-ctx K []

-- Contexts of the hole in a computation term context
-- (the absolute version, it includes Γ as its prefix)

abs-hole-ctx : ∀ {Γ f C} → Γ ⊢K[ f ]⦂ C → Ctx
abs-hole-ctx {Γ} K = rel-hole-ctx K Γ

-- Relating the absolute and relative versions of hole-ctx

rel-hole-ctx-++ᶜ : ∀ {Γ Γ' Γ'' f C}
                 → (K : Γ ⊢K[ f ]⦂ C)
                 → rel-hole-ctx K (Γ' ++ᶜ Γ'') ≡ Γ' ++ᶜ rel-hole-ctx K Γ''

rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} []ₖ =
  refl
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (K ₖ[ p ]; N) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (M ;[ p ]ₖ K) =
  rel-hole-ctx-++ᶜ K 
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (match V `in[ p ]ₖ K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (perform[ p ]ₖ op V K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (handle[ p ]ₖ K `with H `in N) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (handle M `with H `in[ p ]ₖ K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (delay[ p ]ₖ τ K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (unbox[ p ]ₖ q V K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (box[ p ]ₖ V K) =
  rel-hole-ctx-++ᶜ K

hole-ctx-++ᶜ : ∀ {Γ f C}
             → (K : Γ ⊢K[ f ]⦂ C)
             → abs-hole-ctx K ≡ Γ ++ᶜ hole-ctx K

hole-ctx-++ᶜ {Γ} K = rel-hole-ctx-++ᶜ {Γ} {Γ} {[]} K

-- Monotonicity if computation term contexts with respect to flags

◁-mon : ∀ {Γ C f f'}
      → f ≤ᶠ f'
      → Γ ⊢K[ f ]⦂ C
      → Γ ⊢K[ f' ]⦂ C
      
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

-- Renaming of computation term contexts

K-rename : ∀ {Γ Γ' C f}
         → Ren Γ Γ'
         → Γ ⊢K[ f ]⦂ C
         ---------------
         → Γ' ⊢K[ f ]⦂ C

K-rename ρ []ₖ =
  []ₖ
K-rename ρ (K ₖ[ p ]; N) =
  (K-rename ρ K) ₖ[ p ]; (C-rename (cong-ren ρ) N)
K-rename ρ (M ;[ p ]ₖ K) =
  (C-rename ρ M) ;[ p ]ₖ (K-rename (cong-ren ρ) K)
K-rename ρ (match V `in[ p ]ₖ K) =
  match (V-rename ρ V) `in[ p ]ₖ (K-rename (cong-ren ρ) K)
K-rename ρ (perform[ p ]ₖ op V K) =
  perform[ p ]ₖ op (V-rename ρ V) (K-rename (cong-ren ρ) K)
K-rename ρ (handle[ p ]ₖ K `with H `in N) =
  handle[ p ]ₖ K-rename ρ K `with (λ op τ'' → C-rename (cong-ren ρ) (H op τ'')) `in (C-rename (cong-ren ρ) N)
K-rename ρ (handle M `with H `in[ p ]ₖ K) =
  handle (C-rename ρ M) `with (λ op τ'' → C-rename (cong-ren ρ) (H op τ'')) `in[ p ]ₖ (K-rename (cong-ren ρ) K)
K-rename ρ (delay[ p ]ₖ τ K) =
  delay[ p ]ₖ τ (K-rename (cong-ren ρ) K)
K-rename ρ (unbox[ p ]ₖ q V K) =
  unbox[ p ]ₖ (≤-trans q (ctx-time-≤ ρ)) (V-rename (ρ -ʳ _ , q) V) (K-rename (cong-ren ρ) K)
K-rename ρ (box[ p ]ₖ V K) =
  box[ p ]ₖ (V-rename (cong-ren ρ) V) (K-rename (cong-ren ρ) K)

-- Composition of computation term contexts

_[_]ₖ : ∀ {Γ C f f'}
      → (K : Γ ⊢K[ f ]⦂ C)
      → (L : Γ ++ᶜ hole-ctx K ⊢K[ f' ]⦂ (hole-ty K))
      → Γ ⊢K[ f ∨ᶠ f' ]⦂ C

[]ₖ [ L ]ₖ =
  ◁-mon ∨ᶠ-inr L
(K ₖ[ p ]; N) [ L ]ₖ =
  (K [ L ]ₖ) ₖ[ ≤ᶠ-trans p ∨ᶠ-inl ]; N
(M ;[ p ]ₖ K) [ L ]ₖ =
  M ;[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ
  (K [ K-rename (eq-ren
         (trans
           (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
           (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) L ]ₖ)
(match V `in[ p ]ₖ K) [ L ]ₖ =
  match V `in[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _ ∷ _) (hole-ctx K))))) L ]ₖ)
perform[ p ]ₖ op V K [ L ]ₖ =
  perform[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ op V
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) L ]ₖ)
handle[ p ]ₖ K `with H `in N [ L ]ₖ =
  handle[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ) `with H `in N
handle M `with H `in[ p ]ₖ K [ L ]ₖ =
  handle M `with H `in[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) L ]ₖ)
delay[ p ]ₖ τ K [ L ]ₖ =
  delay[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ τ
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩) (hole-ctx K))))) L ]ₖ)
unbox[ p ]ₖ q V K [ L ]ₖ =
  unbox[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ q V
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) L ]ₖ)
box[ p ]ₖ V K [ L ]ₖ =
  box[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ V
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) L ]ₖ)

{-
-- Composition of computation term context with absolute binding contexts (leaving it here just in case)

_[_]ₖ : ∀ {Γ C f f'}
      → (K : Γ ⊢K[ f ]⦂ C)
      → (L : abs-hole-ctx K ⊢K[ f' ]⦂ (hole-ty K))
      → Γ ⊢K[ f ∨ᶠ f' ]⦂ C

[]ₖ [ L ]ₖ =
  ◁-mon ∨ᶠ-inr L
(K ₖ[ p ]; N) [ L ]ₖ =
  (K [ L ]ₖ) ₖ[ ≤ᶠ-trans p ∨ᶠ-inl ]; N
(M ;[ p ]ₖ K) [ L ]ₖ =
  M ;[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ)
(match V `in[ p ]ₖ K) [ L ]ₖ =
  match V `in[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ)
perform[ p ]ₖ op V K [ L ]ₖ =
  perform[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ op V (K [ L ]ₖ)
handle[ p ]ₖ K `with H `in N [ L ]ₖ =
  handle[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ) `with H `in N
handle M `with H `in[ p ]ₖ K [ L ]ₖ =
  handle M `with H `in[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ)
delay[ p ]ₖ τ K [ L ]ₖ =
  delay[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ τ (K [ L ]ₖ)
unbox[ p ]ₖ q V K [ L ]ₖ =
  unbox[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ q V (K [ L ]ₖ)
box[ p ]ₖ V K [ L ]ₖ =
  box[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ V (K [ L ]ₖ)
-}

-- Filling a computation term context hole with a computation

_[_] : ∀ {Γ C f} 
     → (K : Γ ⊢K[ f ]⦂ C) 
     → (M : Γ ++ᶜ hole-ctx K ⊢C⦂ (hole-ty K)) 
     → Γ ⊢C⦂ C

[]ₖ [ N ] =
  N
(K ₖ[ p ]; M) [ N ] =
  (K [ N ]) ; M
(M ;[ p ]ₖ K) [ N ] =
  M ;
  (K [ C-rename (eq-ren
         (trans
           (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
           (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) N ])
(match V `in[ p ]ₖ K) [ N ] =
  match V `in
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _ ∷ _) (hole-ctx K))))) N ])
perform[ p ]ₖ op V K [ N ] =
  perform op V
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) N ])
handle[ p ]ₖ K `with H `in M [ N ] =
  handle (K [ N ]) `with H `in M
handle M `with H `in[ p ]ₖ K [ N ] =
  handle M `with H `in
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) N ])
delay[ p ]ₖ τ K [ N ] =
  delay τ
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩) (hole-ctx K))))) N ])
unbox[ p ]ₖ q V K [ N ] =
  unbox q V
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) N ])
box[ p ]ₖ V K [ N ] =
  box V
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) N ])


{-
-- Filling a computation term context hole with a computation with absolute binding context (leaving it here just in case)

_[_] : ∀ {Γ C f} 
     → (K : Γ ⊢K[ f ]⦂ C) 
     → (M : abs-hole-ctx K ⊢C⦂ (hole-ty K)) 
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
-}

