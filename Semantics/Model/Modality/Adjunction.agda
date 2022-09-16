---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past

module Semantics.Model.Modality.Adjunction (Cat : Category)
                                           (Fut : Future Cat)
                                           (Pas : Past Cat) where

open import Util.Equality
open import Util.Time

open Category Cat
open Future Fut
open Past Pas

record Adjunction : Set₁ where

  field

    -- STRUCTURE

    -- Unit of the adjunction

    η⊣ : ∀ {A τ} → A →ᵐ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
    ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵐ A

    -- PROPERTIES

    -- η-⊣ is natural

    η⊣-nat : ∀ {A B τ} → (f : A →ᵐ B)
           → [ τ ]ᶠ (⟨ τ ⟩ᶠ f) ∘ᵐ η⊣ ≡ η⊣ ∘ᵐ f

    -- ε-⊣ is natural

    ε⊣-nat : ∀ {A B τ} → (f : A →ᵐ B)
           → f ∘ᵐ ε⊣ ≡ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f)

    -- Triangle equations of the adjunction
  
    ε⊣∘Fη≡id : ∀ {A τ} → ε⊣ {⟨ τ ⟩ᵒ A} ∘ᵐ ⟨ τ ⟩ᶠ (η⊣ {A}) ≡ idᵐ
    Gε⊣∘η≡id : ∀ {A τ} → [ τ ]ᶠ (ε⊣ {A}) ∘ᵐ η⊣ {[ τ ]ᵒ A} ≡ idᵐ

    -- Interaction between η-⊣/ε-⊣ of the adjunction and η/ε of the modalities

    η⊣≡ε⁻¹∘η : ∀ {A} → η⊣ {A} ≡ ε⁻¹ {⟨ 0 ⟩ᵒ A} ∘ᵐ η {A}
    ε⊣≡ε∘η⁻¹ : ∀ {A} → ε⊣ {A} ≡ ε {A} ∘ᵐ η⁻¹ {[ 0 ]ᵒ A}

    -- Interaction between η-⊣/ε-⊣ of the adjunction and μ/δ of the modalities

    -- TODO


