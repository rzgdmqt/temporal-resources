---------------------------------------
-- Equality related auxiliary proofs --
---------------------------------------

module Util.Equality where

import Relation.Binary.PropositionalEquality as Eq
open Eq public hiding (Extensionality) renaming ([_] to [|_|])

open import Axiom.Extensionality.Propositional

-- Assuming function extensionality

postulate
  fun-ext  : ∀ {a b} → Extensionality a b
  ifun-ext : ∀ {a b} → ExtensionalityImplicit a b

-- Congruence rules for dependent functions

dcong : ∀ {A : Set} {B : A → Set} (f : (x : A) → B x) {x y}
      → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f refl = refl

dcong₂ : ∀ {A : Set} {B : A → Set} {C : Set}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
       → f x₁ y₁ ≡ f x₂ y₂
dcong₂ f refl refl = refl

-- UIP

uip : ∀ {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl
