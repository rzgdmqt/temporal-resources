-------------------------------------------------------------------
-- Types and terms of the intuitionistic variant of the language --
-------------------------------------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

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
  BaseSet  : BaseType → Set

-- Ground types (for operation signatures)

data GType : Set where
  Base  : BaseType → GType                -- base types
  Unit  : GType                           -- unit type
  Empty : GType                           -- empty type

-- Signature of (ground-typed) operation symbols

postulate
  Op         : Set                          -- set of operation symbols
  param      : Op → GType                   -- parameter type of each operation
  arity      : Op → GType                   -- arity type of each operation
  op-time    : Op → Time                    -- each operation's (maximal) time-duration

-- Grammar of value and computation types

mutual

  data VType : Set where
    Base  : BaseType → VType                 -- base types
    Unit  : VType                            -- unit type
    Empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    [_]_  : Time → VType → VType             -- temporal modality: values of type `[ t ] A`
                                             -- become available in at most `t` time steps
  data CType : Set where
    _‼_ : VType → Time → CType

  infix  37 [_]_
  infixr 30 _⇒_
  infix  31 _‼_

-- Conversion of ground types to types

type-of-gtype : GType → VType
type-of-gtype (Base B) = Base B
type-of-gtype Unit     = Unit
type-of-gtype Empty    = Empty

-- Structured contexts (indexed by the number of ◆s in them)

data Ctx : Set where
  []   : Ctx                       -- empty context
  _∷ᶜ_ : Ctx → VType → Ctx          -- context extension with a variable
  _⟨_⟩ : Ctx → Time → Ctx          -- context use after a time delay

infixl 31 _∷ᶜ_
infix  32 _⟨_⟩

-- Concatenation of contexts

_++ᶜ_ : Ctx → Ctx → Ctx
Γ ++ᶜ []         = Γ
Γ ++ᶜ (Γ' ∷ᶜ X)  = (Γ ++ᶜ Γ') ∷ᶜ X
Γ ++ᶜ (Γ' ⟨ τ ⟩) = (Γ ++ᶜ Γ') ⟨ τ ⟩

infixl 30 _++ᶜ_

-- Total time delay of a context 

ctx-delay : Ctx → Time
ctx-delay []        = 0
ctx-delay (Γ ∷ᶜ A)  = ctx-delay Γ
ctx-delay (Γ ⟨ τ ⟩) = ctx-delay Γ + τ

-- Proof that sub-contexts split a given context

data _,_split_ : (Γ Γ' Γ'' : Ctx) → Set where
  split-[] : ∀ {Γ} → Γ , [] split Γ
  split-∷ᶜ : ∀ {Γ Γ' Γ'' A} → Γ , Γ' split Γ'' → Γ , Γ' ∷ᶜ A split Γ'' ∷ᶜ A
  split-⟨⟩ : ∀ {Γ Γ' Γ'' τ} → Γ , Γ' split Γ'' → Γ , Γ' ⟨ τ ⟩ split Γ'' ⟨ τ ⟩

-- Variable in a context (looking under τ-many time delay)

data _∈[_]_ (A : VType) : Time → Ctx → Set where
  Hd    : ∀ {Γ τ}    → A ∈[ τ ] Γ ∷ᶜ A
  Tl-∷ᶜ : ∀ {Γ B τ}  → A ∈[ τ ] Γ → A ∈[ τ ] Γ ∷ᶜ B
  Tl-⟨⟩ : ∀ {Γ τ τ'} → A ∈[ τ' ] Γ → A ∈[ τ + τ' ] Γ ⟨ τ ⟩

infix 27 _∈[_]_

-- Monotonicity of variables in context

--∈[]-monotonicity : ∀ {Γ A τ τ'} → A ∈[ τ ] Γ → τ' ≤ τ → A ∈[ τ' ] Γ
--∈[]-monotonicity Hd        p = Hd
--∈[]-monotonicity (Tl-∷ᶜ x) p = Tl-∷ᶜ (∈[]-monotonicity x p)
--∈[]-monotonicity (Tl-⟨⟩ q x) p = Tl-⟨⟩ {!!} (∈[]-monotonicity x {!!})

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where

    -- variables

    var     : {A : VType}
            → {τ : Time}
            → A ∈[ τ ] Γ
            ------------
            → Γ ⊢V⦂ A

    -- base-typed constants

    const   : {B : BaseType}
            → BaseSet B
            ----------------
            → Γ ⊢V⦂ Base B

    -- unit type

    ⋆       :
            ------------
              Γ ⊢V⦂ Unit

    -- lambda abstraction
          
    lam     : {A : VType}
            → {C : CType}
            → Γ ∷ᶜ A ⊢C⦂ C
            -------------
            → Γ ⊢V⦂ A ⇒ C

    -- boxing up a value/resource that is ready for use in at least `t` time steps

    box     : {A : VType}
            → {τ : Time}
            → Γ ⟨ τ ⟩ ⊢V⦂ A
            ---------------
            → Γ ⊢V⦂ [ τ ] A

  data _⊢C⦂_ (Γ : Ctx) : CType → Set where

    -- returning a value

    return  : {A : VType}
            → {τ : Time}
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ A ‼ τ        -- arbitrary `τ` to push `coerce`s inside computations

    -- sequential composition

    _;_     : {A B : VType}      -- note: use \;0 to get this unicode semicolon
            → {τ τ' : Time}
            → Γ ⊢C⦂ A ‼ τ
            → Γ ∷ᶜ A ⊢C⦂ B ‼ τ'
            -------------------
            → Γ ⊢C⦂ B ‼ (τ + τ') -- TODO: might want this to be arbitrary to compute away coercions

    -- function application
    
    _·_     : {A : VType}
            → {C : CType}
            → Γ ⊢V⦂ A ⇒ C
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ C

    -- empty type elimination

    absurd  : {C : CType}
            → Γ ⊢V⦂ Empty
            -------------
            → Γ ⊢C⦂ C

    -- performing algebraic operations

    perform : {A : VType}
            → {τ : Time}
            → (op : Op)
            → Γ ⊢V⦂ type-of-gtype (param op)
            → Γ ⟨ op-time op ⟩ ∷ᶜ type-of-gtype (arity op) ⊢C⦂ A ‼ τ
            --------------------------------------------------------
            → Γ ⊢C⦂ A ‼ (op-time op + τ)

    -- TODO: in the future, add effect handlers as well

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {Γ' Γ'' : Ctx}
            → {A : VType}
            → {C : CType}
            → {τ : Time}
            → Γ' , Γ'' split Γ
            → τ ≤ ctx-delay Γ''
            → Γ' ⊢V⦂ [ τ ] A
            → Γ ∷ᶜ A  ⊢C⦂ C
            -------------------
            → Γ ⊢C⦂ C                    -- arbitrary `τ'` to push `coerce`s inside (includes 0)

    -- explicit sub-effecting coercion (no general sub-typing for simplicity)

    coerce  : {A : VType}
            → {τ τ' : Time}
            → τ ≤ τ'
            → Γ ⊢C⦂ A ‼ τ
            ---------------
            → Γ ⊢C⦂ A ‼ τ'
