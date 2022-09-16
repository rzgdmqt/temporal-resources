---------------------------------------------
-- Interpretation of base and ground types --
---------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future

module Semantics.Model.BaseGroundTypes (Cat : Category) (Fut : Future Cat) where

open import Util.Operations

open Category Cat
open Future Fut

record BaseGroundTypes : Set₁ where

  field
  
    -- constant TSET (TODO: change to an object for every base type)
    
    ConstTSet : Set → TSet

    -- interpretation of base-typed constants
    
    constᵗ : ∀ {B} → BaseSet B → 𝟙ᵗ →ᵗ ConstTSet (BaseSet B)

  -- extension of base type interpretation to ground types
  
  ⟦_⟧ᵍ : GType → TSet
  ⟦ Base B ⟧ᵍ   = ConstTSet (BaseSet B)
  ⟦ Unit ⟧ᵍ     = 𝟙ᵗ
  ⟦ Empty ⟧ᵍ    = 𝟘ᵗ
  ⟦ [ τ ]ᵍ A ⟧ᵍ = [ τ ]ᵒ ⟦ A ⟧ᵍ
