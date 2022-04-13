---------------------------------------
-- Equational theory of the language --
---------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language
open import ContextModality
open import Renamings
open import Substitutions

module EquationalTheory where

-- Equations between well-typed values and computations

mutual

  data _⊢V⦂_==_ (Γ : Ctx) : {A : VType} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    -- reflexivity, symmetry, transitivity
  
    ⊢V⦂-refl : ∀ {A}
            → (V : Γ ⊢V⦂ A)
            --------------
            → Γ ⊢V⦂ V == V

    ⊢V⦂-sym : ∀ {A}
           → {V W : Γ ⊢V⦂ A}
           → Γ ⊢V⦂ V == W
           ----------------
           → Γ ⊢V⦂ W == V

    ⊢V⦂-trans : ∀ {A}
             → {V W U : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V == W
             → Γ ⊢V⦂ W == U
             -------------------
             → Γ ⊢V⦂ V == U

    -- congruences

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
          -----------------
          → Γ ⊢V⦂ V == ⋆

    lam-eta : ∀ {A C}
            → (V : Γ ⊢V⦂ A ⇒ C)
            --------------------------------------------
            → Γ ⊢V⦂ V == lam (V-rename wk-ren V · var Hd)

  infix 18 _⊢V⦂_==_

  data _⊢C⦂_==_ (Γ : Ctx) : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    -- reflexivity, symmetry, transitivity
  
    ⊢C⦂-refl : ∀ {C}
            → (M : Γ ⊢C⦂ C)
            --------------
            → Γ ⊢C⦂ M == M

    ⊢C⦂-sym : ∀ {C}
           → {M N : Γ ⊢C⦂ C}
           → Γ ⊢C⦂ M == N
           ----------------
           → Γ ⊢C⦂ N == M

    ⊢C⦂-trans : ∀ {C}
             → {M N P : Γ ⊢C⦂ C}
             → Γ ⊢C⦂ M == N
             → Γ ⊢C⦂ N == P
             -------------------
             → Γ ⊢C⦂ M == P

    -- congruences

    -- ...

    -- beta/computational equations

    let-return : ∀ {A B τ}
               → (V : Γ ⊢V⦂ A)
               → (M : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ)
               ----------------------------------------------------------------
               → Γ ⊢C⦂ return V ; M
                   == C-rename ⟨⟩-eta-ren (M [ Hd ↦ V-rename ⟨⟩-eta⁻¹-ren V ]c)   -- M[V/x]

    let-assoc : ∀ {A B C τ τ' τ''}
              → (M : Γ ⊢C⦂ A ‼ τ)
              → (N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
              → (P : Γ ⟨ τ + τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
              ---------------------------------------------------------------
              → Γ ⊢C⦂ (M ; N) ; P
                  == coerce (≤-reflexive (sym (+-assoc τ τ' τ'')))                -- M ; (N ; P)
                       (M ;
                         (N ;
                           C-rename (cong-ren {Γ'' = [] ⟨ τ' ⟩ ∷ B} wk-ren ∘ʳ
                             cong-ren {Γ'' = [] ∷ B} ⟨⟩-mu-ren ) P))
                  
    let-perform : ∀ {A B τ τ'}
                → (op : Op)
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                ---------------------------------------------------------------
                → Γ ⊢C⦂ (perform op V M) ; N
                    == coerce (≤-reflexive (sym (+-assoc (op-time op) τ τ')))     -- perform op V (M ; N)
                         (perform op V
                           (M ;
                             C-rename ((cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} wk-ren ∘ʳ
                               cong-ren {Γ'' = [] ∷ A} ⟨⟩-mu-ren )) N))

    let-coerce : ∀ {A B τ τ' τ''}
               → (p : τ ≤ τ')
               → (M : Γ ⊢C⦂ A ‼ τ)
               → (N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'')
               --------------------------------
               → Γ ⊢C⦂ coerce p M ; C-rename (cong-ren {Γ'' = [] ∷ A} (⟨⟩-mon-ren p)) N
                   == coerce {!!} (M ; N)

    -- ...

    -- eta equations

    -- ...

    -- coercion equations

    -- ...

  infix 18 _⊢C⦂_==_
