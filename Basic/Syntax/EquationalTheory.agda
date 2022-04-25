---------------------------------------
-- Equational theory of the language --
---------------------------------------

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions

open import Util.Operations
open import Util.Time

module Syntax.EquationalTheory where

-- Explicit sub-effecting, derived from delaying

n≤m⇒m≡n+n' : ∀ {n m} → n ≤ m → Σ[ n' ∈ ℕ ] m ≡ n + n'
n≤m⇒m≡n+n' z≤n = _ , refl
n≤m⇒m≡n+n' (s≤s p) with n≤m⇒m≡n+n' p
... | n' , q = n' , cong suc q

coerce : ∀ {Γ A τ τ'}
       → τ ≤ τ'
       → Γ ⊢C⦂ A ‼ τ
       ---------------
       → Γ ⊢C⦂ A ‼ τ'

coerce p M =
  delay
    ([] ⟨ proj₁ (n≤m⇒m≡n+n' p) ⟩)
    (proj₂ (n≤m⇒m≡n+n' p))
    (C-rename wk-⟨⟩-ren M)

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

    -- congruence equations

    lam-cong : ∀ {A B τ}
             → {M N : Γ ∷ A ⊢C⦂ B ‼ τ}
             → Γ ∷ A ⊢C⦂ M == N
             -------------------------
             → Γ ⊢V⦂ lam M == lam N

    box-cong : ∀ {A τ}
             → {V W : Γ ⟨ τ ⟩ ⊢V⦂ A}
             → Γ ⟨ τ ⟩ ⊢V⦂ V == W
             -----------------------
             → Γ ⊢V⦂ box V == box W

    -- eta equations

    ⋆-eta : (V : Γ ⊢V⦂ Unit)
          ------------------
          → Γ ⊢V⦂ V == ⋆

    lam-eta : ∀ {A C}
            → (V : Γ ⊢V⦂ A ⇒ C)
            ---------------------------------------------
            → Γ ⊢V⦂ V == lam (V-rename wk-ren V · var Hd)

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

    -- congruence equations

    return-cong : ∀ {A}
                → {V W : Γ ⊢V⦂ A}
                → Γ ⊢V⦂ V == W
                ----------------------------
                → Γ ⊢C⦂ return V == return W

    ;-cong : ∀ {A B τ τ'}
           → {M M' : Γ ⊢C⦂ A ‼ τ}
           → {N N' : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'}
           → Γ ⊢C⦂ M == M'
           → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ N == N'
           ---------------------------------
           → Γ ⊢C⦂ M ; N == (M' ; N')

    ·-cong : ∀ {A C}
           → {V V' : Γ ⊢V⦂ A ⇒ C}
           → {W W' : Γ ⊢V⦂ A}
           ------------------------
           → Γ ⊢C⦂ V · W == V' · W'

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
                ----------------------------------------------
                → Γ ⊢C⦂ handle M `with H `in N == handle M' `with H' `in N'

    unbox-cong : ∀ {Γ' Γ'' A C τ}
               → {p q : Γ' , Γ'' split Γ}                   -- proof-irrelevant, no need for p ≡ q assumption 
               → {r s : τ ≤ ctx-time Γ''}                   -- proof-irrelevant, no need for r ≡ s assumption
               → {V W : Γ' ⊢V⦂ [ τ ] A}
               → {M N : Γ ∷ A  ⊢C⦂ C}
               → Γ' ⊢V⦂ V == W
               → Γ ∷ A ⊢C⦂ M == N
               --------------------------------------
               → Γ ⊢C⦂ unbox p r V M == unbox q s W N
    
    delay-cong  : ∀ {A τ τ' τs τs'}
                → {p : τ' ≡ τ + tctx-time τs}                      -- proof-irrelevant, no need for p ≡ q assumption
                → {q : τ' ≡ τ + tctx-time τs'}                      -- proof-irrelevant, no need for p ≡ q assumption
                → {M : Γ ++ᶜ tctx-ctx τs ⊢C⦂ A ‼ τ}
                → {N : Γ ++ᶜ tctx-ctx τs' ⊢C⦂ A ‼ τ}
                → (r : τs ≡ τs')
                → Γ ++ᶜ tctx-ctx τs ⊢C⦂ M == C-rename (eq-ren (sym (cong (λ τs → Γ ++ᶜ tctx-ctx τs) r))) N
                ------------------------------------------------------------------------------------------
                → Γ ⊢C⦂ delay τs p M == delay τs' q N

    -- computational/beta equations for sequential composition

    ;-return : ∀ {A B τ}
             → (V : Γ ⊢V⦂ A)
             → (M : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ)
             ----------------------------------------------------------------
             → Γ ⊢C⦂ return V ; M
                 == C-rename ⟨⟩-η-ren (M [ Hd ↦ V-rename ⟨⟩-η⁻¹-ren V ]c)   -- M[V/x]
                  
    ;-perform : ∀ {A B τ τ'}
              → (op : Op)
              → (V : Γ ⊢V⦂ type-of-gtype (param op))
              → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
              → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
              -----------------------------------------------------------------------------------------------------
              → Γ ⊢C⦂ (perform op V M) ; N
                  == coerce (≤-reflexive (sym (+-assoc (op-time op) τ τ')))
                       (perform op V
                          (M ;
                           C-rename (cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} wk-ren ∘ʳ
                               cong-ren {Γ'' = [] ∷ A} ⟨⟩-μ-ren)
                           N))

    -- associativity equation for sequential composition

    ;-assoc : ∀ {A B C τ τ' τ''}
            → (M : Γ ⊢C⦂ A ‼ τ)
            → (N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
            → (P : Γ ⟨ τ + τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
            -----------------------------------------------------------------------------------
            → Γ ⊢C⦂ (M ; N) ; P
                == coerce (≤-reflexive (sym (+-assoc τ τ' τ'')))
                     (M ; (N ; C-rename (cong-ren {Γ'' = [] ⟨ τ' ⟩ ∷ B} wk-ren ∘ʳ
                                 cong-ren {Γ'' = [] ∷ B} ⟨⟩-μ-ren ) P))

    -- computational/beta equation for function application

    ·-lam : ∀ {A C}
          → (M : Γ ∷ A ⊢C⦂ C)
          → (W : Γ ⊢V⦂ A)
          ------------------------
          → Γ ⊢C⦂ lam M · W == (M [ Hd ↦ W ]c)

    -- computational/beta equations for effect handling

    handle-return : ∀ {A B τ'}
                  → (V : Γ ⊢V⦂ A)
                  → (H : (op : Op) → (τ'' : Time) →
                           Γ ∷ type-of-gtype (param op)
                             ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                           ⊢C⦂ B ‼ (op-time op + τ''))
                  → (N : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ')
                  ---------------------------------------------------
                  → Γ ⊢C⦂ handle return V `with H `in N
                      == (C-rename ⟨⟩-η-ren (N [ Hd ↦ V-rename ⟨⟩-η⁻¹-ren V ]c))

    handle-op : ∀ {A B τ τ'}
              → (op : Op)
              → (V : Γ ⊢V⦂ type-of-gtype (param op))
              → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
              → (H : (op : Op) → (τ'' : Time) →
                       Γ ∷ type-of-gtype (param op)
                         ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                       ⊢C⦂ B ‼ (op-time op + τ''))
              → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
              ------------------------------------------------------------------------------------------
              → Γ ⊢C⦂ handle perform op V M `with H `in N
                  == coerce
                       (≤-reflexive (sym (+-assoc (op-time op) τ τ')))
                       (H op (τ + τ')
                         [ Tl-∷ Hd ↦ V ]c
                         [ Hd ↦ box (lam (handle M
                                          `with (λ op' τ'' →
                                                  C-rename
                                                    (cong-ren {Γ'' = [] ∷ _ ∷ [ _ ] (_ ⇒ _)} wk-ctx-ren)
                                                    (H op' τ''))
                                          `in (C-rename
                                                (cong-ren {Γ'' = [] ∷ A}
                                                  (   cong-ren {Γ'' = [] ⟨ τ ⟩} wk-ren
                                                   ∘ʳ ⟨⟩-μ-ren))
                                                N))) ]c)
                                                
    -- computational/beta equation for unboxing

    unbox-box : ∀ {Γ' Γ'' A B τ τ'}
              → (p : Γ' , Γ'' split Γ)
              → (q : τ ≤ ctx-time Γ'')
              → (V : Γ' ⟨ τ ⟩ ⊢V⦂ A)
              → (N : Γ ∷ A ⊢C⦂ B ‼ τ')
              ---------------------------------------------------
              → Γ ⊢C⦂ unbox p q (box V) N
                  == (N [ Hd ↦ V-rename (wk-⟨⟩-ctx-ren p q) V ]c)

    -- eta equations

    ;-eta : ∀ {A τ}
          → (M : Γ ⊢C⦂ A ‼ τ)
          -----------------------------------------------------------------
          → Γ ⊢C⦂ M
              == coerce (≤-reflexive (+-identityʳ τ)) (M ; return (var Hd))
              
    absurd-eta : ∀ {C}
               → (V : Γ ⊢V⦂ Empty)
               → (M : Γ ⊢C⦂ C)
               ---------------------
               → Γ ⊢C⦂ absurd V == M

    box-unbox-eta : ∀ {Γ' A C τ}
                  → (p : Γ' , [] ⟨ τ ⟩ split Γ )
                  → (V : Γ' ⊢V⦂ [ τ ] A)
                  → (M : Γ' ⟨ τ ⟩ ∷ [ τ ] A ⊢C⦂ C)
                  -------------------------------------------------
                  → Γ ⊢C⦂ C-rename                                                     -- M[V/y]
                            (eq-ren (split-≡ p))                                       
                            (M [ Hd ↦ V-rename wk-⟨⟩-ren V ]c)                                          
                      == unbox p ≤-refl                                               -- unbox V to x in M[box x/y]                             
                           V
                           (C-rename (eq-ren (split-≡ (split-∷ p)))
                             ((C-rename (exch-ren ∘ʳ wk-ren) M)
                                [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c))

    -- coercion equations
    
    delay-[] : ∀ {A τ}
             → (M : Γ ⊢C⦂ A ‼ τ)
             ---------------------------------------------
             → Γ ⊢C⦂ delay [] (sym (+-identityʳ τ)) M == M
    
    delay-trans : ∀ {A τ τ' τ'' τs₁ τs₂}
                → (p : τ' ≡ τ + tctx-time τs₁)
                → (q : τ'' ≡ (τ + tctx-time τs₁) + tctx-time τs₂)
                → (M : Γ ++ᶜ tctx-ctx τs₂ ++ᶜ tctx-ctx τs₁ ⊢C⦂ A ‼ τ)
                ---------------------------------------------------------------------------
                → Γ ⊢C⦂ delay τs₂ (trans q (cong (_+ tctx-time τs₂) (sym p))) (delay τs₁ p M)
                    == delay
                         (τs₂ ++ᶜᵗ τs₁)
                         (trans
                           q
                           (trans
                             (+-assoc τ (tctx-time τs₁) (tctx-time τs₂))
                             (trans
                               (cong (τ +_) (+-comm (tctx-time τs₁) (tctx-time τs₂)))
                               (cong (τ +_) (sym (++ᶜ-tctx-time τs₂ τs₁))))))
                         (C-rename
                           (eq-ren
                             (trans
                               (++ᶜ-assoc Γ (tctx-ctx τs₂) (tctx-ctx τs₁))
                               (cong (Γ ++ᶜ_) (sym (++ᶜ-tctx-ctx τs₂ τs₁)))))
                           M)
    
    ;-delay₁ : ∀ {A B τ τ' τ'' τs}
             → (p : τ' ≡ τ + tctx-time τs)
             → (M : Γ ++ᶜ tctx-ctx τs ⊢C⦂ A ‼ τ)
             → (N : Γ ⟨ τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
             -------------------------------------------------------------------
             → Γ ⊢C⦂ delay τs p M ; N
                 == delay τs
                      (trans
                        (cong (_+ τ'') p)
                        (trans
                          (+-assoc τ (tctx-time τs) τ'')
                          (trans
                            (cong (τ +_) (+-comm (tctx-time τs) τ''))
                            (sym (+-assoc τ τ'' (tctx-time τs))))))
                      (M ;
                       C-rename
                         (cong-∷-ren
                           (   cong-⟨⟩-ren (wk-⟨⟩-tctx-ren τs)
                            ∘ʳ ⟨⟩-μ-ren {τ = tctx-time τs} {τ' = τ}
                            ∘ʳ ⟨⟩-≤-ren (≤-reflexive
                                 (trans p (+-comm τ (tctx-time τs))))))
                       N)
    {-
    ;-delay₂ : ∀ {A B τ τ' τ''' τs}
             → (p : τ''' ≡ τ' + tctx-time τs)
             → (M : Γ ⊢C⦂ A ‼ τ)
             → (N : Γ ⟨ τ ⟩ ++ᶜ tctx-ctx τs ∷ A ⊢C⦂ B ‼ τ')                            -- unfortunately cannot assume x:A between the ⟨_⟩s
             -------------------------------------------------------------             -- because otherwise cannot type the RHS of the equation, 
             → Γ ⊢C⦂ M ; delay τs p (C-rename (exch-⟨⟩-tctx-var-ren τs) N)              -- though then the LHS wouldn't have a renaming in it
                 == delay τs
                      {!!}
                      (C-rename wk-ctx-ren M ;
                       C-rename {!!} N)
    -}
    
    perform-delay : ∀ {A τ τ'' τs}
                  → (p : τ'' ≡ τ + tctx-time τs)
                  → (op : Op)
                  → (V : Γ ⊢V⦂ type-of-gtype (param op))
                  → (M : Γ ⟨ op-time op ⟩ ++ᶜ tctx-ctx τs ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)        -- same as above regarding var. not being betweel ⟨_⟩s
                  -----------------------------------------------------------------------------
                  → Γ ⊢C⦂ perform op V (delay τs p (C-rename (exch-⟨⟩-tctx-var-ren τs) M))
                      == delay τs
                           {!!}
                           (perform op
                             {!!}
                             {!!})                      
    {-
    handle-delay : ∀ {A B τ τ' τ'' τ'''}
                 → (p : τ'' ≡ τ + τ')
                 → (M : Γ ⟨ τ' ⟩ ⊢C⦂ A ‼ τ)
                 → (H : (op : Op) → (τ'''' : Time) →
                          Γ ∷ type-of-gtype (param op)
                            ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'''')
                          ⊢C⦂ B ‼ (op-time op + τ''''))
                 → (N : Γ ⟨ τ'' ⟩ ∷ A ⊢C⦂ B ‼ τ''')
                 --------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle delay τ' p M `with H `in N
                     == delay τ'
                          (trans
                            (cong (_+ τ''') p)
                            (trans
                              (trans
                                (+-assoc τ τ' τ''')
                                (cong (τ +_) (+-comm τ' τ''')))
                              (sym (+-assoc τ τ''' τ'))))
                          (handle M
                           `with (λ op τ'''' →
                                   C-rename
                                     (cong-ren {Γ'' = [] ∷ _ ∷ _} (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren))
                                     (H op τ''''))
                           `in (C-rename
                                 (cong-ren {Γ'' = [] ∷ A}
                                   (⟨⟩-μ-ren ∘ʳ ⟨⟩-≤-ren (≤-reflexive (trans p (+-comm τ τ')))))
                                 N))
  -}
  infix 18 _⊢C⦂_==_

