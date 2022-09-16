---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past

module Semantics.Model.Modality.Adjunction
  (Cat : Category) (Fut : Future Cat) (Pas : Past Cat) where

open import Util.Time

open Category Cat
open Future Fut
open Past Pas

record Adjunction : Set₁ where

  field

    -- STRUCTURE

    -- Unit of the adjunction

    η⊣ : ∀ {A τ} → A →ᵗ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
    ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵗ A

    -- PROPERTIES

    -- η-⊣ is natural

    η⊣-nat : ∀ {A B τ} → (f : A →ᵗ B)
           → [ τ ]ᶠ (⟨ τ ⟩ᶠ f) ∘ᵗ η⊣ ≡ᵗ η⊣ ∘ᵗ f

    -- ε-⊣ is natural

    ε⊣-nat : ∀ {A B τ} → (f : A →ᵗ B)
           → f ∘ᵗ ε⊣ ≡ᵗ ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f)

    -- Triangle equations of the adjunction
  
    ε⊣∘Fη≡id : ∀ {A τ} → ε⊣ {⟨ τ ⟩ᵒ A} ∘ᵗ ⟨ τ ⟩ᶠ (η⊣ {A}) ≡ᵗ idᵗ
    Gε⊣∘η≡id : ∀ {A τ} → [ τ ]ᶠ (ε⊣ {A}) ∘ᵗ η⊣ {[ τ ]ᵒ A} ≡ᵗ idᵗ

    -- Interaction between η-⊣/ε-⊣ of the adjunction and η/ε of the modalities

    η⊣≡ε⁻¹∘η : ∀ {A} → η⊣ {A} ≡ᵗ ε⁻¹ {⟨ 0 ⟩ᵒ A} ∘ᵗ η {A}
    ε⊣≡ε∘η⁻¹ : ∀ {A} → ε⊣ {A} ≡ᵗ ε {A} ∘ᵗ η⁻¹ {[ 0 ]ᵒ A}

    -- Interaction between η-⊣/ε-⊣ of the adjunction and μ/δ of the modalities

    -- TODO


