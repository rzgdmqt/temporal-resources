---------------------------------------------
-- Interpretation of base and ground types --
---------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.BaseGroundTypes (Cat : Category) where

open import Util.Operations

open Category Cat

record BaseGroundTypes : Set₁ where

  field
  
    -- CONSTANT TSET (TODO: change to an object for every base type)
    ConstTSet : Set → TSet

    -- INTERPRETATION OF BASE-TYPED CONSTANTS
    constᵗ : ∀ {B} → BaseSet B → 𝟙ᵗ →ᵗ ConstTSet (BaseSet B)

{-
  ⟦_⟧ᵍ : GType → TSet
  ⟦ Base B ⟧ᵍ   = ConstTSet (BaseSet B)
  ⟦ Unit ⟧ᵍ     = 𝟙ᵗ
  ⟦ Empty ⟧ᵍ    = 𝟘ᵗ
  ⟦ [ τ ]ᵍ A ⟧ᵍ = [ τ ]ᵒ ⟦ A ⟧ᵍ
-}
