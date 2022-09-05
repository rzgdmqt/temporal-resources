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

-- Constant subst is identity

subst-const : ∀ {A : Set} (P : Set) {x₁ x₂ : A}
            → (p : x₁ ≡ x₂)
            → (y : P)
            → subst (λ _ → P) p y ≡ y
subst-const P refl y = refl

-- Dependent double substitution

dsubst₂ : ∀ {A : Set} {B : A → Set}
          (P : (x : A) → B x → Set)
          {x₁ x₂ y₁ y₂}
        → (p : x₁ ≡ x₂)
        → subst B p y₁ ≡ y₂
        → P x₁ y₁
        → P x₂ y₂
dsubst₂ P refl refl z = z

-- Tertiary congruence

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v z w} → x ≡ y → u ≡ v → z ≡ w → f x u z ≡ f y v w
cong₃ f refl refl refl = refl

dcong₃ : ∀ {A : Set} {B : A → Set} {C : (x : A) → B x → Set} {D : Set}
         (f : (x : A) → (y : B x) → C x y → D) {x₁ x₂ y₁ y₂ z₁ z₂}
       → (p : x₁ ≡ x₂) → (q : subst B p y₁ ≡ y₂) → dsubst₂ C p q z₁ ≡ z₂
       → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
dcong₃ f refl refl refl = refl

-- UIP

uip : ∀ {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl
