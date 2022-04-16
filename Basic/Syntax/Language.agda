-------------------------------------------------
-- Types and well-typed syntax of the language --
-------------------------------------------------

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Syntax.Operations

open import Util.Time

module Syntax.Language where

-- Value and computation types

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

-- Embedding ground types into types

type-of-gtype : GType → VType
type-of-gtype (Base B) = Base B
type-of-gtype Unit     = Unit
type-of-gtype Empty    = Empty

-- Structured contexts

data Ctx : Set where
  []   : Ctx                       -- empty context
  _∷_  : Ctx → VType → Ctx         -- context extension with a variable
  _⟨_⟩ : Ctx → Time → Ctx          -- using context after time-passage

infixl 31 _∷_
infix  32 _⟨_⟩

∷ᶜ-injective : ∀ {Γ Γ' A} → Γ ∷ A ≡ Γ' ∷ A → Γ ≡ Γ'
∷ᶜ-injective refl = refl

⟨⟩-injective : ∀ {Γ Γ' τ} → Γ ⟨ τ ⟩ ≡ Γ' ⟨ τ ⟩ → Γ ≡ Γ'
⟨⟩-injective refl = refl

-- Concatenation of contexts

_++ᶜ_ : Ctx → Ctx → Ctx
Γ ++ᶜ []         = Γ
Γ ++ᶜ (Γ' ∷ X)   = (Γ ++ᶜ Γ') ∷ X
Γ ++ᶜ (Γ' ⟨ τ ⟩) = (Γ ++ᶜ Γ') ⟨ τ ⟩

infixl 30 _++ᶜ_

-- Identity, associativity, and injectivity of ++ᶜ

++ᶜ-identityˡ : ∀ {Γ} → [] ++ᶜ Γ ≡ Γ
++ᶜ-identityˡ {[]}      = refl
++ᶜ-identityˡ {Γ ∷ A}   = cong (_∷ A) ++ᶜ-identityˡ
++ᶜ-identityˡ {Γ ⟨ τ ⟩} = cong (_⟨ τ ⟩) ++ᶜ-identityˡ

++ᶜ-identityʳ : ∀ {Γ} → Γ ++ᶜ [] ≡ Γ
++ᶜ-identityʳ = refl

++ᶜ-assoc : (Γ Γ' Γ'' : Ctx) → (Γ ++ᶜ Γ') ++ᶜ Γ'' ≡ Γ ++ᶜ (Γ' ++ᶜ Γ'')
++ᶜ-assoc Γ Γ' []          = refl
++ᶜ-assoc Γ Γ' (Γ'' ∷ A)   = cong (_∷ A) (++ᶜ-assoc Γ Γ' Γ'')
++ᶜ-assoc Γ Γ' (Γ'' ⟨ τ ⟩) = cong (_⟨ τ ⟩) (++ᶜ-assoc Γ Γ' Γ'')

-- Amount of time-passage modelled by a context 

ctx-time : Ctx → Time
ctx-time []        = 0
ctx-time (Γ ∷ A)   = ctx-time Γ
ctx-time (Γ ⟨ τ ⟩) = ctx-time Γ + τ

-- Interaction of time-passage and ++ᶜ

ctx-time-++ᶜ : (Γ Γ' : Ctx)
              → ctx-time (Γ ++ᶜ Γ') ≡ ctx-time Γ + ctx-time Γ'
ctx-time-++ᶜ Γ []         = sym (+-identityʳ (ctx-time Γ))
ctx-time-++ᶜ Γ (Γ' ∷ A)   = ctx-time-++ᶜ Γ Γ'
ctx-time-++ᶜ Γ (Γ' ⟨ τ ⟩) = trans
                               (cong (_+ τ) (ctx-time-++ᶜ Γ Γ'))
                               (+-assoc (ctx-time Γ) (ctx-time Γ') τ)

-- Proof that sub-contexts split a given context

data _,_split_ : (Γ Γ' Γ'' : Ctx) → Set where
  split-[] : ∀ {Γ} → Γ , [] split Γ
  split-∷  : ∀ {Γ Γ' Γ'' A} → Γ , Γ' split Γ'' → Γ , Γ' ∷ A split Γ'' ∷ A
  split-⟨⟩ : ∀ {Γ Γ' Γ'' τ} → Γ , Γ' split Γ'' → Γ , Γ' ⟨ τ ⟩ split Γ'' ⟨ τ ⟩

-- Interaction between context splitting and ++ᶜ 

split-≡ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → Γ₁ ++ᶜ Γ₂ ≡ Γ
split-≡ split-[]     = refl
split-≡ (split-∷ p)  = cong (_∷ _) (split-≡ p)
split-≡ (split-⟨⟩ p) = cong (_⟨ _ ⟩) (split-≡ p)

≡-split : ∀ {Γ Γ₁ Γ₂} → Γ₁ ++ᶜ Γ₂ ≡ Γ → Γ₁ , Γ₂ split Γ
≡-split {Γ₂ = []}       refl = split-[]
≡-split {Γ₂ = Γ₂ ∷ A}   refl = split-∷ (≡-split refl)
≡-split {Γ₂ = Γ₂ ⟨ τ ⟩} refl = split-⟨⟩ (≡-split refl)

split-≡-++ᶜ : ∀ {Γ₁ Γ₂} → Γ₁ , Γ₂ split (Γ₁ ++ᶜ Γ₂)
split-≡-++ᶜ = ≡-split refl

-- Variable in a context (under τ-amount of time-passage)

data _∈[_]_ (A : VType) : Time → Ctx → Set where
  Hd    : ∀ {Γ}      → A ∈[ 0 ] Γ ∷ A
  Tl-∷  : ∀ {Γ B τ}  → A ∈[ τ ] Γ → A ∈[ τ ] Γ ∷ B
  Tl-⟨⟩ : ∀ {Γ τ τ'} → A ∈[ τ' ] Γ → A ∈[ τ + τ' ] Γ ⟨ τ ⟩

infix 27 _∈[_]_

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

    -- TODO: in the future, add effect handlers as well

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    unbox   : {Γ' Γ'' : Ctx}
            → {A : VType}
            → {C : CType}
            → {τ : Time}
            → Γ' , Γ'' split Γ
            → τ ≤ ctx-time Γ''
            → Γ' ⊢V⦂ [ τ ] A
            → Γ ∷ A  ⊢C⦂ C
            ------------------
            → Γ ⊢C⦂ C

    -- explicit delaying of a computation (a special case of this
    -- construct is the explicit sub-effecting subsumption rule)

    -- note: the delay in the context is needed to type equations
    -- such as (delay p M) ; N == delay (p + id) (M ; N)

    delay   : {A : VType}
            → {τ τ'' : Time}
            → (τ' : Time)
            → τ'' ≡ τ + τ'
            → Γ ⟨ τ' ⟩ ⊢C⦂ A ‼ τ
            --------------------
            → Γ ⊢C⦂ A ‼ τ''
