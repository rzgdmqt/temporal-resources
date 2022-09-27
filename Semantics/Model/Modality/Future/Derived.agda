------------------------------------------------------------------------
-- Semantics of the future modality `[ t ] A` as a strong monoidal    --
-- functor indexed by (ℕ,≤). It is the analogue of the comonadic      --
-- □-modality on types/formulae in Fitch-style modal lambda calculi.  --
--                                                                    --
-- Note: While `[ t ] A` is a strong monoidal functor, then below we  --
-- use the terminology (counit, comultiplication) of graded comonads. --
------------------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future

module Semantics.Model.Modality.Future.Derived (Cat : Category)
                                               (Fut : Future Cat) where

open import Util.Equality
open import Util.Time

open Category Cat
open Future Fut

open import Semantics.Model.Category.Derived Cat

-- Unit

η-[] : ∀ {A τ} → A →ᵐ [ τ ]ᵒ A
η-[] {A} {τ} = []-≤ {A = A} z≤n ∘ᵐ ε⁻¹
