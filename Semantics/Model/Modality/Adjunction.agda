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

    -- η⊣ is natural

    η⊣-nat : ∀ {A B τ} → (f : A →ᵐ B)
           → [ τ ]ᶠ (⟨ τ ⟩ᶠ f) ∘ᵐ η⊣ ≡ η⊣ ∘ᵐ f

    -- ε⊣ is natural

    ε⊣-nat : ∀ {A B τ} → (f : A →ᵐ B)
           → f ∘ᵐ ε⊣ ≡ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f)

    -- Triangle equations of the adjunction
  
    ε⊣∘Fη⊣≡id : ∀ {A τ} → ε⊣ {⟨ τ ⟩ᵒ A} ∘ᵐ ⟨ τ ⟩ᶠ (η⊣ {A}) ≡ idᵐ
    Gε⊣∘η⊣≡id : ∀ {A τ} → [ τ ]ᶠ (ε⊣ {A}) ∘ᵐ η⊣ {[ τ ]ᵒ A} ≡ idᵐ

    -- Interaction between η⊣/ε⊣ of the adjunction and η/ε of the modalities

    η⊣-≤ : ∀ {A τ}
         → [ τ ]ᶠ (⟨⟩-≤ z≤n) ∘ᵐ η⊣ {A} {τ}
         ≡ []-≤ z≤n ∘ᵐ ε⁻¹ {⟨ 0 ⟩ᵒ A} ∘ᵐ η {A}

    ε⊣-≤ : ∀ {A τ}
         → ⟨ 0 ⟩ᶠ ([]-≤ z≤n) ∘ᵐ η ∘ᵐ ε⁻¹ ∘ᵐ ε⊣ {A} {τ}
         ≡ ⟨⟩-≤ z≤n

    -- Interaction between η⊣/ε⊣ of the adjunction and μ/δ of the modalities

    GGμ∘Gη⊣∘η⊣≡δ∘η⊣ : ∀ {A τ τ'}
                    → [ τ ]ᶠ ([ τ' ]ᶠ (⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ)) ∘ᵐ [ τ ]ᶠ η⊣ ∘ᵐ η⊣ {A}
                    ≡ δ ∘ᵐ η⊣

    ε⊣∘Fε⊣∘FFδ≡ε⊣∘μ : ∀ {A τ τ'}
                    → ε⊣ {A} ∘ᵐ ⟨ τ ⟩ᶠ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ (⟨ τ' ⟩ᶠ (δ ∘ᵐ []-≤ (≤-reflexive (+-comm τ τ'))))
                    ≡ ε⊣ ∘ᵐ μ

