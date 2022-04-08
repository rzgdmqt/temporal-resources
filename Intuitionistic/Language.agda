-------------------------------------------------------------------
-- Types and terms of the intuitionistic variant of the language --
-------------------------------------------------------------------

open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

module Language where

-- Time steps and annotations

Time : Set
Time = ℕ

-- Base types

postulate
  BaseType : Set

-- Ground types (for operation signatures)

data GType : Set where
  Base  : BaseType → GType                -- base types
  Unit  : GType                           -- unit type
  Empty : GType                           -- empty type

-- Signature of (ground-typed) operation symbols

postulate
  Op    : Set                             -- set of operation symbols
  param : Op → GType                      -- parameter type of each operation
  arity : Op → GType                      -- arity type of each operation
  top   : Op → Time                       -- each operation's (maximal) time-duration

-- Grammar of types

data Type : Set where
  Base  : BaseType → Type                 -- base types
  Unit  : Type                            -- unit type
  Empty : Type                            -- empty type
  _⇒_‼_ : Type → Type → Time → Type       -- function type
  [_]_  : Time → Type → Type              -- temporal modality: values of type `[ t ] A`
                                          -- become available in at most `t` time steps

infix  37 [_]_
infixr 30 _⇒_‼_

type-of-gtype : GType → Type
type-of-gtype (Base b) = Base b
type-of-gtype Unit     = Unit
type-of-gtype Empty    = Empty

-- Structured contexts (indexed by the number of ◆s in them)

data Ctx : Set where
  []   : Ctx                       -- empty context
  _∷ᶜ_ : Ctx → Type → Ctx          -- context extension with a variable
  _⟨_⟩ : Ctx → Time → Ctx          -- context use after a time delay

infixl 29 _∷ᶜ_
infix  28 _⟨_⟩

-- Concatenation of contexts

_++ᶜ_ : Ctx → Ctx → Ctx
Γ ++ᶜ []         = Γ
Γ ++ᶜ (Γ' ∷ᶜ X)  = Γ ++ᶜ Γ' ∷ᶜ X
Γ ++ᶜ (Γ' ⟨ t ⟩) = Γ ++ᶜ Γ' ⟨ t ⟩

infixl 30 _++ᶜ_

-- Total time delay of a context 

delayᶜ : Ctx → Time
delayᶜ []        = 0
delayᶜ (Γ ∷ᶜ A)  = delayᶜ Γ
delayᶜ (Γ ⟨ t ⟩) = delayᶜ Γ + t

-- Variable in a context (if it is available now)

data _∈_ (A : Type) : Ctx → Set where
  Hd    : ∀ {Γ}   → A ∈ Γ ∷ᶜ A
  Tl    : ∀ {Γ B} → A ∈ Γ → A ∈ Γ ∷ᶜ B
  Tl-⟨⟩ : ∀ {Γ}   → A ∈ Γ → A ∈ Γ ⟨ 0 ⟩

infix 27 _∈_

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_‼_

mutual

  data _⊢V⦂_ (Γ : Ctx) : Type → Set where

    -- variables

    var    : {A : Type} 
           → A ∈ Γ
           -----------
           → Γ ⊢V⦂ A

    -- lambda abstraction
          
    lam    : {A B : Type}
           → {t : Time}
           → Γ ∷ᶜ A ⊢C⦂ B ‼ t
           ------------------
           → Γ ⊢V⦂ A ⇒ B ‼ t

    -- boxing up a value for use in at least `t` time steps

    box    : {A : Type}
           → {t : Time}
           → Γ ⟨ t ⟩ ⊢V⦂ A
           ---------------
           → Γ ⊢V⦂ [ t ] A

  data _⊢C⦂_‼_ (Γ : Ctx) : Type → Time → Set where

    -- returning a value

    return : {A : Type}
           → Γ ⊢V⦂ A
           -------------
           → Γ ⊢C⦂ A ‼ 0        -- TODO: might want this to be arbitrary to compute away coercions

    -- sequential composition

    _>>=_  : {A B : Type}
           → {t t' : Time}
           → Γ ⊢C⦂ A ‼ t
           → Γ ∷ᶜ A ⊢C⦂ B ‼ t'
           -------------------
           → Γ ⊢C⦂ B ‼ (t + t') -- TODO: might want this to be arbitrary to compute away coercions

    -- function application
    
    _·_    : {A B : Type}
           → {t : Time}
           → Γ ⊢V⦂ A ⇒ B ‼ t
           → Γ ⊢V⦂ A
           -----------------
           → Γ ⊢C⦂ B ‼ t

    -- performing algebraic operations

    perform : {A : Type}
            → {t : Time}
            → (op : Op)
            → Γ ⊢V⦂ type-of-gtype (param op)
            → Γ ∷ᶜ type-of-gtype (arity op) ⊢C⦂ A ‼ t
            ----------------------------------------
            → Γ ⊢C⦂ A ‼ (top op + t)

    -- unboxing a `t`-boxed value after at least `t` time steps

    unbox  : {Γ' Γ'' : Ctx}
           → {A : Type}
           → {t : Time}
           → Γ' ⊢V⦂ [ t ] A
           → Γ ≡ Γ' ++ᶜ Γ''
           → t ≤ delayᶜ Γ''
           ----------------
           → Γ ⊢C⦂ A ‼ 0       -- TODO: might want this to be arbitrary to compute away coercions










{-

-- Well-typed terms

infix 26 _⊢_

data _⊢_ (Γ : Ctx) : Type → Set where

  -- variables

  var    : {A : Type} 
         → A ∈ Γ
         -----------
         → Γ ⊢ A

  -- function type
          
  lam    : {A B : Type}
         → Γ ∷ᶜ A ⊢ B
         --------------
         → Γ ⊢ A ⇒ B
          
  _·_    : {A B : Type}
         → Γ ⊢ A ⇒ B
         → Γ ⊢ A
         --------------
         → Γ ⊢ B

  -- temporal modality

  delay  : {A : Type}
         → {t : Time}
         → Γ ⟨ t ⟩ ⊢ A
         -------------- (delay computing the value by `t` time steps)
         → Γ ⊢ [ t ] A

  wait   : {Γ' Γ'' : Ctx}
         → {A : Type}
         → {t : Time}
         → Γ' ⊢ [ t ] A
         → Γ ≡ Γ' ++ᶜ Γ''
         → t ≤ delayᶜ Γ''
         ---------------- (wait for a value to become available after at least `t` time steps)
         → Γ ⊢ A

-}
