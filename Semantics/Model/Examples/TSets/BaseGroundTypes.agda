---------------------------------------------
-- Interpretation of base and ground types --
---------------------------------------------

module Semantics.Model.Examples.TSets.BaseGroundTypes where

open import Function

open import Semantics.Model.Examples.TSets.TSets

open import Util.Operations
open import Util.Equality

-- Constant time-varying sets

ConstTSet : Set → TSet
ConstTSet A = tset (λ _ → A) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

-- Base-typed constants as elements

constᵗ : ∀ {B} → BaseSet B → 𝟙ᵗ →ᵗ ConstTSet (BaseSet B)
constᵗ c =
  tset-map
    (λ _ → c)
    (λ p _ → refl)
