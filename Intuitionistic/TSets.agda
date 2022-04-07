open import Function

open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

-- Time-indexed sets and modalities on them
-------------------------------------------

module TSets where

-- Time steps (using natural numbers)

Time : Set
Time = ℕ

-- Time-indexed sets

record TSet : Set₁ where
  constructor
    tset
  field
    carrier  : Time → Set
    monotone : ∀ {t t'} → t ≤ t' → carrier t → carrier t'

    -- TODO: also include the functor laws for refl-id and trans-∘

open TSet

record _→ᵗ_ (A B : TSet) : Set where
  constructor
    tset-map
  field
    carrier : ∀ {t} → carrier A t → carrier B t

    -- TODO: also include naturality law

open _→ᵗ_

-- semantics of `[ t ] A` modality as a graded comonad

[_]ᵒ : Time → TSet → TSet
[ t ]ᵒ (tset A Af) =
  tset (λ t' → Σ[ t'' ∈ Time ] (t'' ≤ t × t'' ≤ t' × A t''))
       (λ r → λ { (t'' , p , q , a) → t'' , p , ≤-trans q r , a })

[_]ᶠ : ∀ {A B} → (t : Time) → A →ᵗ B → [ t ]ᵒ A →ᵗ [ t ]ᵒ B
[ t ]ᶠ (tset-map f) = tset-map (λ { (t'' , p , q , a) → t'' , p , q , f a })

[_]-≤ : ∀ {A t t'} → t ≤ t' → [ t ]ᵒ A →ᵗ [ t' ]ᵒ A
[ p ]-≤ = tset-map (λ { (t'' , q , r , a) → t'' , ≤-trans q p , r , a })

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {tset A Af} = tset-map (λ { (t'' , p , q , a) → Af q a })

ε' : ∀ {A t} → [ t ]ᵒ A →ᵗ A
ε' {tset A Af} = tset-map λ { (t'' , p , q , a) → Af q a } -- wouldn't want this to be the case!

δ : ∀ {A t₁ t₂} → [ t₁ + t₂ ]ᵒ A →ᵗ [ t₁ ]ᵒ ([ t₂ ]ᵒ A)
δ {tset A Af} {t₁} {t₂} =
  tset-map δ-aux --(λ {t'} → λ { (t'' , p , q , a) → {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} })

  where
    δ-aux : {t' : Time} → carrier ([ t₁ + t₂ ]ᵒ (tset A Af)) t' → carrier ([ t₁ ]ᵒ ([ t₂ ]ᵒ (tset A Af))) t'
    δ-aux {t'} (t'' , p , q , a) with t'' <ᵇ t₁ | inspect (λ (t'' , t₁) → t'' <ᵇ t₁) (t'' , t₁)
    ... | true  | [ eq ]  = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
    ... | false | [ eq ]  = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

-- ∸

{-
[_]ᶠ : ∀ {A B} → (t : Time) → A →ᵗ B → [ t ]ᵒ A →ᵗ [ t ]ᵒ B
[ t ]ᶠ f p = f ∘ p

[_]-≤ : ∀ {A t t'} → t ≤ t' → [ t ]ᵒ A →ᵗ [ t' ]ᵒ A
[ p ]-≤ q = λ r → q (≤-trans p r)

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε p = p z≤n

δ : ∀ {A t t'} → [ t + t' ]ᵒ A →ᵗ [ t ]ᵒ ([ t' ]ᵒ A)
δ p = λ q r → p {!!}
-}

-- ...

-- semantics of `Γ ⟨ t ⟩` modality as a graded monad

-- ...
