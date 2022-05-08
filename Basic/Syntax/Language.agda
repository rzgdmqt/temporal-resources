---------------------------------------
-- Well-typed syntax of the language --
---------------------------------------

open import Syntax.Types
open import Syntax.Contexts

open import Util.Equality
open import Util.Operations
open import Util.Time

module Syntax.Language where

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
            → Γ ∷ A ⊢C⦂ C
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
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ A ‼ 0

    -- sequential composition
    
    _;_     : {A B : VType}      -- note: use \;0 to get this unicode semicolon
            → {τ τ' : Time}
            → Γ ⊢C⦂ A ‼ τ
            → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
            ------------------------
            → Γ ⊢C⦂ B ‼ (τ + τ')
    
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
            → Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ
            -------------------------------------------------------
            → Γ ⊢C⦂ A ‼ (op-time op + τ)

    -- effect handling

    handle_`with_`in
            : {A B : VType}
            → {τ τ' : Time}
            → Γ ⊢C⦂ A ‼ τ
            → ((op : Op) → (τ'' : Time) →                                  -- more formally there should be a
                 Γ ∷ type-of-gtype (param op)                              -- parametricity condition here as
                   ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')   -- well on the quantified time τ''
                 ⊢C⦂ B ‼ (op-time op + τ''))
            → Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ'
            --------------------------------------------------
            → Γ ⊢C⦂ B ‼ (τ + τ')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {A : VType}
            → {C : CType}
            → {τ : Time}
            → τ ≤ ctx-time Γ
            → Γ -ᶜ τ ⊢V⦂ [ τ ] A
            → Γ ∷ A  ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C

    -- explicit delaying of a computation

    delay   : {A : VType}
            → {τ' τ'' : Time}
            → (τ : Time)
            → τ'' ≡ τ + τ'               -- abstracting τ + τ' into a separate variable for inductive
            → Γ ⟨ τ ⟩ ⊢C⦂ A ‼ τ'          -- proofs, and to support equational rewriting the time gradings
            --------------------
            → Γ ⊢C⦂ A ‼ τ''
