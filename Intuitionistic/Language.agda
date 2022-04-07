open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

-- Types and terms of the intuitionistic variant of the language
----------------------------------------------------------------

module Language where

-- Time steps (using natural numbers)

Time : Set
Time = ℕ

-- Base types

postulate BaseType : Set

-- Grammar of types

data Type : Set where
  Base  : BaseType → Type          -- base types
  _⇒_   : Type → Type → Type       -- function type
  [_]_  : Time → Type → Type       -- temporal modality: values of type `[ t ] A`
                                   -- become available in at most `t` time steps

infix  37 [_]_
infixr 30 _⇒_

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

delay : Ctx → Time
delay []        = 0
delay (Γ ∷ᶜ A)  = delay Γ
delay (Γ ⟨ t ⟩) = delay Γ + t

-- Variable in a context (if it is available now)

data _∈_ (A : Type) : Ctx → Set where
  Hd    : ∀ {Γ}   → A ∈ Γ ∷ᶜ A
  Tl    : ∀ {Γ B} → A ∈ Γ → A ∈ Γ ∷ᶜ B
  Tl-⟨⟩ : ∀ {Γ}   → A ∈ Γ → A ∈ Γ ⟨ 0 ⟩

infix 27 _∈_

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

  give   : {A : Type}
         → {t : Time}
         → Γ ⟨ t ⟩ ⊢ A
         -------------- (make a value available after `t` time steps)
         → Γ ⊢ [ t ] A

  wait   : {Γ' Γ'' : Ctx}
         → {A : Type}
         → {t : Time}
         → Γ' ⊢ [ t ] A
         → Γ ≡ Γ' ++ᶜ Γ''
         → t ≤ delay Γ''
         ---------------- (wait for a value to become available in at least `t` time steps)
         → Γ ⊢ A
