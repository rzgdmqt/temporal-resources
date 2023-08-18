---------------------------------------
-- Equational theory of the language --
---------------------------------------

module Syntax.EquationalTheory where

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.CompContext
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Equations between well-typed values and computations

mutual

  -- value equations

  data _⊢V⦂_==_ (Γ : Ctx) : {A : VType} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    -- reflexivity, symmetry, transitivity
  
    V-refl : ∀ {A}
           → {V : Γ ⊢V⦂ A}
           ---------------
           → Γ ⊢V⦂ V == V

    V-sym : ∀ {A}
          → {V W : Γ ⊢V⦂ A}
          → Γ ⊢V⦂ V == W
          -----------------
          → Γ ⊢V⦂ W == V

    V-trans : ∀ {A}
            → {V W U : Γ ⊢V⦂ A}
            → Γ ⊢V⦂ V == W
            → Γ ⊢V⦂ W == U
            -------------------
            → Γ ⊢V⦂ V == U

    -- substitutivity

    V-subst : ∀ {Γ' A B τ}
            → {V W : Γ' ⊢V⦂ B}
            → (p : Γ' ⊢V⦂ V == W)
            → (x : A ∈[ τ ] Γ')
            → (q : proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ≡ Γ)
            → (U : proj₁ (var-split x) ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢V⦂ subst (_⊢V⦂ B) q (V [ x ↦ U ]v)
                == subst (_⊢V⦂ B) q (W [ x ↦ U ]v)

    -- congruence equations

    ⦉⦊-cong : ∀ {A B}
           → {V V' : Γ ⊢V⦂ A}
           → {W W' : Γ ⊢V⦂ B}
           → Γ ⊢V⦂ V == V'
           → Γ ⊢V⦂ W == W'
           ------------------------------
           → Γ ⊢V⦂ ⦉ V , W ⦊ == ⦉ V' , W' ⦊

    lam-cong : ∀ {A B τ}
             → {M N : Γ ∷ A ⊢C⦂ B ‼ τ}
             → Γ ∷ A ⊢C⦂ M == N
             -------------------------
             → Γ ⊢V⦂ lam M == lam N


    -- eta equations

    unit-eta : (V : Γ ⊢V⦂ Unit)
             ------------------
             → Γ ⊢V⦂ V == ⋆

    fun-eta : ∀ {A C}
            → (V : Γ ⊢V⦂ A ⇒ C)
            ---------------------------------------------
            → Γ ⊢V⦂ V
                == lam (V-rename wk-ren V · var Hd)

  infix 18 _⊢V⦂_==_

  -- computation equations

  data _⊢C⦂_==_ (Γ : Ctx) : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    -- reflexivity, symmetry, transitivity
  
    C-refl : ∀ {C}
           → {M : Γ ⊢C⦂ C}
           ---------------
           → Γ ⊢C⦂ M == M

    C-sym : ∀ {C}
          → {M N : Γ ⊢C⦂ C}
          → Γ ⊢C⦂ M == N
          -----------------
          → Γ ⊢C⦂ N == M

    C-trans : ∀ {C}
            → {M N P : Γ ⊢C⦂ C}
            → Γ ⊢C⦂ M == N
            → Γ ⊢C⦂ N == P
            -------------------
            → Γ ⊢C⦂ M == P

    -- substitutivity

    C-subst : ∀ {Γ' A C τ}
            → {M N : Γ' ⊢C⦂ C}
            → (p : Γ' ⊢C⦂ M == N)
            → (x : A ∈[ τ ] Γ')
            → (q : proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ≡ Γ)
            → (V : proj₁ (var-split x) ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢C⦂ subst (_⊢C⦂ C) q (M [ x ↦ V ]c)
                == subst (_⊢C⦂ C) q (N [ x ↦ V ]c)

    -- congruence equations

    return-cong : ∀ {A}
                → {V W : Γ ⊢V⦂ A}
                → Γ ⊢V⦂ V == W
                ----------------------------
                → Γ ⊢C⦂ return V == return W

    seq-cong : ∀ {A B τ τ'}
             → {M M' : Γ ⊢C⦂ A ‼ τ}
             → {N N' : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'}
             → Γ ⊢C⦂ M == M'
             → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ N == N'
             ---------------------------------
             → Γ ⊢C⦂ M ; N == (M' ; N')

    app-cong : ∀ {A C}
             → {V V' : Γ ⊢V⦂ A ⇒ C}
             → {W W' : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V == V'
             → Γ ⊢V⦂ W == W'
             ------------------------
             → Γ ⊢C⦂ V · W == V' · W'

    match-cong : ∀ {A B C}
               → {V W : Γ ⊢V⦂ A |×| B}
               → {M N : Γ ∷ A ∷ B ⊢C⦂ C}
               → Γ ⊢V⦂ V == W
               → Γ ∷ A ∷ B ⊢C⦂ M == N
               --------------------------------------
               → Γ ⊢C⦂ match V `in M == match W `in N 

    absurd-cong : ∀ {C}
                → {V W : Γ ⊢V⦂ Empty}
                → Γ ⊢V⦂ V == W
                ------------------------------------
                → Γ ⊢C⦂ absurd {C = C} V == absurd W

    perform-cong : ∀ {A τ op}
                 → {V W : Γ ⊢V⦂ type-of-gtype (param op)}
                 → {M N : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ}
                 → Γ ⊢V⦂ V == W
                 → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ M == N
                 ---------------------------------------------------------------
                 → Γ ⊢C⦂ perform op V M == perform op W N

    delay-cong  : ∀ {A τ τ'}
                → {M N : Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ'}
                → Γ ⟨ τ ⟩ ⊢C⦂ M == N
                ------------------------------
                → Γ ⊢C⦂ delay {τ' = τ'} τ M == delay τ N

    handle-cong : ∀ {A B τ τ'}
                → {M M' : Γ ⊢C⦂ A ‼ τ}
                → {H H' : ((op : Op) → (τ'' : Time) → 
                             Γ ∷ type-of-gtype (param op)
                               ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                             ⊢C⦂ B ‼ (op-time op + τ''))}
                → {N N' : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'}
                → Γ ⊢C⦂ M == M'
                → ((op : Op) → (τ'' : Time) →
                     Γ ∷ type-of-gtype (param op)
                       ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                     ⊢C⦂ H op τ'' == H' op τ'')
                → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ N == N'
                --------------------------------------------------------------------
                → Γ ⊢C⦂ handle M `with H `in N == handle M' `with H' `in N'

    unbox-cong : ∀ {A C τ}
               → {V W : Γ -ᶜ τ ⊢V⦂ [ τ ] A}
               → {M N : Γ ∷ A  ⊢C⦂ C}
               → {p q : τ ≤ ctx-time Γ}
               → Γ -ᶜ τ ⊢V⦂ V == W
               → Γ ∷ A ⊢C⦂ M == N
               ----------------------------------
               → Γ ⊢C⦂ unbox p V M == unbox q W N

    box-cong : ∀ {A B τ τ'}
             → {V W : Γ ⟨ τ ⟩ ⊢V⦂ A}
             → {M N : Γ ∷ [ τ ] A ⊢C⦂ B ‼ τ' }
             → Γ ⟨ τ ⟩ ⊢V⦂ V == W
             → Γ ∷ [ τ ] A ⊢C⦂ M == N
             --------------------------
             → Γ ⊢C⦂ box V M == box W N
                    
    -- computational/beta-equations for sequential composition

    seq-return : ∀ {A B τ}
               → (V : Γ ⊢V⦂ A)
               → (M : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ)
               -----------------------------------------------------
               → Γ ⊢C⦂ return V ; M
                   == (C-rename (cong-∷-ren ⟨⟩-η-ren) M) [ Hd ↦ V ]c
                  
    seq-perform : ∀ {A B τ τ'}
                → (op : Op)
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                --------------------------------------------------------------
                → Γ ⊢C⦂ (perform op V M) ; N
                    == τ-subst (sym (+-assoc (op-time op) τ τ'))
                         (perform op V
                            (M ;
                             C-rename ((cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)))
                             N))

    seq-delay : ∀ {A B τ τ' τ''}
              → (M : Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ')
              → (N : Γ ⟨ τ + τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
              -------------------------------------------------------
              → Γ ⊢C⦂ delay τ M ; N
                  == τ-subst (sym (+-assoc τ τ' τ''))
                       (delay τ
                         (M ;
                          C-rename (cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren) 
                          N))

    seq-box : ∀ {A B C τ τ' τ''}
              → (V : Γ ⟨ τ ⟩ ⊢V⦂ A)
              → (M : Γ ∷ [ τ ] A ⊢C⦂ B ‼ τ')
              → (N : Γ ⟨ τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
              -------------------------------------------------------
              → Γ ⊢C⦂ box V M ; N 
                  == box V (M ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    seq-unbox : ∀ {A B C τ τ' τ''}
              → (p : τ ≤ ctx-time Γ)
              → (V : Γ -ᶜ τ  ⊢V⦂ [ τ ] A)
              → (M : Γ ∷ A ⊢C⦂ B ‼ τ')
              → (N : Γ ⟨ τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
              -------------------------------------------------------
              → Γ ⊢C⦂ unbox p V M ; N 
                  == unbox p V (M ; C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    -- eta-equation for sequential composition

    seq-eta : ∀ {A τ}
            → (M : Γ ⊢C⦂ A ‼ τ)
            ---------------------------------------------------
            → Γ ⊢C⦂ M
                == τ-subst (+-identityʳ τ) (M ; return (var Hd))

    -- associativity equation for sequential composition

    seq-assoc : ∀ {A B C τ τ' τ''}
              → (M : Γ ⊢C⦂ A ‼ τ)
              → (N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
              → (P : Γ ⟨ τ + τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
              ---------------------------------------------------------------------
              → Γ ⊢C⦂ (M ; N) ; P
                  == τ-subst (sym (+-assoc τ τ' τ''))
                       (M ; (N ; C-rename (cong-ren {Γ'' = [] ⟨ τ' ⟩ ∷ B} wk-ren ∘ʳ
                                   cong-ren {Γ'' = [] ∷ B} ⟨⟩-μ-ren ) P))

    -- computational/beta-equation for function application

    fun-beta : ∀ {A C}
             → (M : Γ ∷ A ⊢C⦂ C)
             → (W : Γ ⊢V⦂ A)
             ----------------------
             → Γ ⊢C⦂ lam M · W
                 == M [ Hd ↦ W ]c

    -- beta-equation for pattern-matching

    match-beta : ∀ {A B C}
               → (V : Γ ⊢V⦂ A)
               → (W : Γ ⊢V⦂ B)
               → (M : Γ ∷ A ∷ B ⊢C⦂ C)
               ------------------------------------
               → Γ ⊢C⦂ match ⦉ V , W ⦊ `in M
                   == M [ Hd ↦ V-rename wk-ren W ]c
                        [ Hd ↦ V ]c

    -- eta-equation for pattern-matching

    match-eta : ∀ {A B C}
              → (V : Γ ⊢V⦂ A |×| B)
              → (M : Γ ∷ A |×| B ⊢C⦂ C)
              -------------------------------------------------------------
              → Γ ⊢C⦂ match V `in
                       (C-rename (exch-ren ∘ʳ wk-ren ∘ʳ exch-ren ∘ʳ wk-ren)
                         M [ Hd ↦ ⦉ var (Tl-∷ Hd) , var Hd ⦊ ]c)
                  == M [ Hd ↦ V ]c

    -- eta-equation for empty type elimination
    
    absurd-eta : ∀ {C}
               → (V : Γ ⊢V⦂ Empty)
               → (M : Γ ∷ Empty ⊢C⦂ C)
               -----------------------
               → Γ ⊢C⦂ absurd V
                   == M [ Hd ↦ V ]c

    -- computational/beta-equations for effect handling

    handle-return : ∀ {A B τ'}
                  → (V : Γ ⊢V⦂ A)
                  → (H : (op : Op) → (τ'' : Time) →
                           Γ ∷ type-of-gtype (param op)
                             ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                           ⊢C⦂ B ‼ (op-time op + τ''))
                  → (N : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ')
                  ----------------------------------------------------------------
                  → Γ ⊢C⦂ handle return V `with H `in N
                      == (C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c)
                      
    handle-perform : ∀ {A B τ τ'}
                    → (op : Op)
                    → (V : Γ ⊢V⦂ type-of-gtype (param op))
                   → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                   → (H : (op : Op) → (τ'' : Time) →
                            Γ ∷ type-of-gtype (param op)
                              ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                            ⊢C⦂ B ‼ (op-time op + τ''))
                   → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                   ----------------------------------------------------------------
                   → Γ ⊢C⦂ handle perform op V M `with H `in N 
                      == box (lam 
                        (handle M 
                        `with (λ op₁ τ'' → 
                            C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren))) 
                            (H op₁ τ'')) 
                        `in (C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)) 
                          N))) 
                        ((τ-subst ((sym (+-assoc (op-time op) τ τ'))) 
                        (H op (τ + τ')) 
                          [ Tl-∷ Hd ↦ V ]c))

    
    handle-delay : ∀ {A B τ τ' τ''}
                 → (M : Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ')
                 → (H : (op : Op) → (τ''' : Time) →
                          Γ ∷ type-of-gtype (param op)
                            ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ''')
                          ⊢C⦂ B ‼ (op-time op + τ'''))
                 → (N : Γ ⟨ τ + τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle delay τ M `with H `in N
                     == τ-subst (sym (+-assoc τ τ' τ''))
                          (delay τ
                            (handle M
                              `with (λ op τ''' →
                                C-rename
                                  (cong-ren {Γ'' = [] ∷ _ ∷ _} (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren))
                                  (H op τ'''))
                              `in (C-rename
                                    (cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren)
                                    N)))

    handle-box : ∀ {A B C τ τ' τ''}
                 → (V : Γ ⟨ τ ⟩ ⊢V⦂ A)
                 → (M : Γ ∷ [ τ ] A ⊢C⦂ B ‼ τ')
                 → (H : (op : Op) → (τ''' : Time) →
                          Γ ∷ type-of-gtype (param op)
                            ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ C ‼ τ''')
                          ⊢C⦂ C ‼ (op-time op + τ'''))
                 → (N : Γ ⟨ τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle box V M `with H `in N
                     == box V 
                        (handle M `with 
                          (λ op τ''' → 
                            C-rename 
                              (cong-∷-ren (cong-∷-ren wk-ren)) 
                              (H op τ''')) 
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))


    handle-unbox : ∀ {A B C τ τ' τ''}
                 → (p : τ ≤ ctx-time Γ)
                 → (V : Γ -ᶜ τ ⊢V⦂ [ τ ] A)
                 → (M : Γ ∷ A ⊢C⦂ B ‼ τ')
                 → (H : (op : Op) → (τ''' : Time) →
                          Γ ∷ type-of-gtype (param op)
                            ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ C ‼ τ''')
                          ⊢C⦂ C ‼ (op-time op + τ'''))
                 → (N : Γ ⟨ τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle unbox p V M `with H `in N
                     == unbox p V 
                        (handle M `with 
                          (λ op τ''' → 
                            C-rename 
                              (cong-∷-ren (cong-∷-ren wk-ren)) 
                              (H op τ''')) 
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))

    -- beta rule for unbox

    unbox-beta : ∀ {Δ A B C τ τ'}
               → (p : τ ≤ ctx-time (BCtx→Ctx Δ))
               → (V : Γ ⟨ τ ⟩ ⊢V⦂ A )
               → (K : Γ ∷ [ τ ] A ⊢K[ Δ ⊢ C ]⦂ B ‼ τ')
               → (N : (Γ ∷ [ τ ] A ⋈ Δ) ∷ A ⊢C⦂ C)
               -----------------------------------------------
               → Γ ⊢C⦂ box V 
                      (K ₖ[ 
                          unbox (τΔ≤τΓ⋈Δ {Γ = Γ ∷ [ τ ] A} {Δ = Δ} p) 
                                (var (proj₂ (proj₂ (var-rename (Γ⋈Δ-ᶜτ {Δ = Δ} p) Hd)))) 
                                N 
                          ]) 
                    == box V (K ₖ[ N [ Hd ↦ V-rename (renΓ⟨τ⟩-Γ⋈Δ {Δ = Δ} p) V ]c ])

    -- unboxing non-related values commute

    unbox-comm : ∀ {A B C τ τ' τ''} →
                (p : τ ≤ ctx-time Γ) → 
                (q : τ' ≤ ctx-time Γ) → 
                (V : Γ -ᶜ τ ⊢V⦂ [ τ ] A) → 
                (W : Γ -ᶜ τ' ⊢V⦂ [ τ' ] B) → 
                (M : Γ ∷ A ∷ B ⊢C⦂ C ‼ τ'') → 
                ---------------------------------------------
                Γ ⊢C⦂ unbox p V 
                        (unbox q (V-rename (wk-ren -ʳ τ') W) M) 
                    ==  unbox q W 
                        (unbox p 
                            (V-rename ((wk-ren -ʳ τ)) V) 
                            (C-rename exch-ren M))

    -- boxing resources commute 

    box-comm : ∀ {A B C τ τ' τ''} → 
              (V : Γ ⟨ τ ⟩ ⊢V⦂ A) →
              (W : Γ ⟨ τ' ⟩ ⊢V⦂ B) → 
              (M : Γ ∷ [ τ ] A ∷ [ τ' ] B ⊢C⦂ C ‼ τ'') → 
              ----------------------------------------
              Γ ⊢C⦂ box V 
                      (box (V-rename (cong-⟨⟩-ren wk-ren) W) M)
                  == box W 
                      (box 
                        (V-rename (cong-⟨⟩-ren wk-ren) V) 
                        (C-rename exch-ren M))

    -- eta rule for box
    -- we don't have garbage collector, so this rule 
    -- is not coverd by operational semantic, since boxed resource
    -- remains in state.
    -- boxed-not-used : ∀ {A C τ τ'} → 
    --                 (V : Γ ⟨ τ ⟩ ⊢V⦂ A) → 
    --                 (M : Γ ⊢C⦂ C ‼ τ') → 
    --                 --------------------
    --                 Γ ⊢C⦂ box V (C-rename wk-ren M)
    --                     == M
    
    -- eta rule for unbox

    unbox-not-used : ∀ {A C τ τ'} → 
                    (p : τ ≤ ctx-time Γ) → 
                    (V : Γ -ᶜ τ ⊢V⦂ [ τ ] A) → 
                    (M : Γ ⊢C⦂ C ‼ τ') → 
                    --------------------
                    Γ ⊢C⦂ unbox p V (C-rename wk-ren M)
                        == M

    -- boxing and unboxing unrelated resources commute
    
    box-unbox-comm : ∀ {A B C τ τ' τ''} → 
                    (p : τ' ≤ ctx-time Γ) → 
                    (V : Γ ⟨ τ ⟩ ⊢V⦂ A) → 
                    (W : Γ -ᶜ τ' ⊢V⦂ [ τ' ] B) → 
                    (M : Γ ∷ [ τ ] A ∷ B ⊢C⦂ C ‼ τ'') → 
                    -----------------------------------
                    Γ ⊢C⦂ box V 
                            (unbox p 
                              (V-rename (wk-ren -ʳ τ') W) 
                              M) 
                        == unbox p 
                            W 
                            (box 
                              (V-rename (cong-⟨⟩-ren wk-ren) V) 
                              (C-rename exch-ren M))    

    delay-zero : ∀ {A τ}
               → (M : Γ ⟨ 0 ⟩ ⊢C⦂ A ‼ τ)
               --------------------------
               → Γ ⊢C⦂ delay 0 M
                   == C-rename ⟨⟩-η-ren M
               
    delay-delay : ∀ {A τ τ₁ τ₂}
                → (M : Γ ⟨ τ₁ ⟩ ⟨ τ₂ ⟩ ⊢C⦂ A ‼ τ)
                ------------------------------------
                → Γ ⊢C⦂ delay τ₁ (delay τ₂ M)
                    == τ-subst
                         (+-assoc τ₁ τ₂ τ)
                         (delay
                           (τ₁ + τ₂)
                           (C-rename ⟨⟩-μ⁻¹-ren M))

  infix 18 _⊢C⦂_==_