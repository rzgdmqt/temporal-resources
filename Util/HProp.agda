module Util.HProp where

open import Level

open import Data.Product hiding (∃)
open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Util.Equality

-- Propositions are (Set₀) types with at most one inhabitant
 
is-proposition : Set → Set
is-proposition A = (x y : A) → x ≡ y
 
-- Truncation structure

postulate
  ∥_∥ : Set → Set
  ∥∥-is-proposition : {A : Set} → is-proposition ∥ A ∥
  ∣_∣ : {A : Set} → A → ∥ A ∥
  ∥∥-elim : {A : Set} {B : Set} → is-proposition B → (A → B) → ∥ A ∥ → B
 
infix 0 ∥_∥

-- Computation rule for truncation

∥∥-compute : {A : Set} {B : Set}
          → (i : (x y : B) → x ≡ y) (p : A → B) (a : A)
          → ∥∥-elim i p ∣ a ∣ ≡ p a
∥∥-compute i p a = i (∥∥-elim i p ∣ a ∣) (p a)

-- Propositions

record HProp : Set₁ where
  constructor ⟨_,_⟩
  field
    proof : Set
    is-prop : is-proposition proof

open HProp public


-- Logic of propositions

-- truth

⊤ʰ : HProp
⊤ʰ = ⟨ ⊤ , (λ _ _ → refl) ⟩

-- falsehood

⊥ʰ : HProp
⊥ʰ = ⟨ ⊥ , (λ x y → ⊥-elim x) ⟩

-- conjunction

_∧ʰ_ : HProp → HProp → HProp
⟨ p , ξ ⟩ ∧ʰ ⟨ q , ζ ⟩ = ⟨ p × q , θ ⟩
  where
    θ : (x y : p × q) → x ≡ y
    θ (x₁ , y₁) (x₂ , y₂) with ξ x₁ x₂ | ζ y₁ y₂
    ... | refl | refl = refl

infixr 6 _∧ʰ_

-- disjunction

_∨ʰ_ : HProp → HProp → HProp
⟨ p , ξ ⟩ ∨ʰ ⟨ q , ζ ⟩ = ⟨ ∥ p ⊎ q ∥ , θ ⟩
  where
    θ : is-proposition ∥ p ⊎ q ∥
    θ = ∥∥-is-proposition

infixr 5 _∨ʰ_

-- implication

_⇒ʰ_ : HProp → HProp → HProp
⟨ p , ξ ⟩ ⇒ʰ ⟨ q , ζ ⟩ = ⟨ (p → q) , θ ⟩
  where
    θ : is-proposition (p → q)
    θ f g = fun-ext λ x → ζ(f x) (g x)

infixr 4 _⇒ʰ_

-- existential quantification

∃ʰ : (A : Set) → (A → HProp) → HProp
∃ʰ A ϕ = ⟨ ∥ Σ[ x ∈ A ] proof (ϕ x) ∥ , ∥∥-is-proposition ⟩

syntax ∃ʰ A (λ x → B) = ∃ʰ[ x ∈ A ] B

-- universal quantification

∀ʰ : (A : Set) → (A → HProp) → HProp
∀ʰ A ϕ = ⟨ (∀ x → proof (ϕ x)) , (λ f g → fun-ext (λ x → is-prop (ϕ x) (f x) (g x))) ⟩

syntax ∀ʰ A (λ x → B) = ∀ʰ[ x ∈ A ] B
