---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction

module Semantics.Model.Modality.Adjunction.Derived (Cat : Category)
                                                   (Fut : Future Cat)
                                                   (Pas : Past Cat)
                                                   (Adj : Adjunction Cat Fut Pas) where

open import Util.Equality
open import Util.Time

open Category Cat
open Future Fut
open Past Pas
open Adjunction Adj

open import Semantics.Model.Category.Derived Cat

-- [_]ᵒ is monoidal (with respect to ×ᵐ)
 
[]-monoidal : ∀ {A B τ}
            → [ τ ]ᵒ A ×ᵐ [ τ ]ᵒ B →ᵐ [ τ ]ᵒ (A ×ᵐ B)

[]-monoidal {A} {B} {τ} =
     [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ ,
              ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
  ∘ᵐ η⊣ {τ = τ}
