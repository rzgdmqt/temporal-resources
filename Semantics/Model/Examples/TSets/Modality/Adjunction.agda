---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

module Semantics.Model.Examples.TSets.Modality.Adjunction where

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

open import Syntax.Language

open import Semantics.Model.Examples.TSets.TSets

open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past

open import Util.Equality
open import Util.Time

-- STRUCTURE

-- Unit of the adjunction

η⊣ : ∀ {A τ} → A →ᵗ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
η⊣ {A} {τ} =
  tset-map
    (λ {t'} a →
      m≤n+m τ t' ,
      monotone A (≤-reflexive (sym (m+n∸n≡m t' τ))) a)
    (λ p x →
      cong₂ _,_
        (≤-irrelevant _ _)
        (trans
          (monotone-trans A _ _ x)
          (trans
            (cong (λ s → monotone A s x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ x)))))

-- Counit of the adjunction

ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵗ A
ε⊣ {A} {τ} =
  tset-map
    (λ { {t'} (p , a) → monotone A (n≤m⇒m∸n+n≤m τ t' p) a })
    (λ { p (q , x) →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ s → monotone A s x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))) })


-- PROPERTIES

-- η-⊣ is natural

η⊣-nat : ∀ {A B τ} → (f : A →ᵗ B)
       → [ τ ]ᶠ (⟨ τ ⟩ᶠ f) ∘ᵗ η⊣ ≡ᵗ η⊣ ∘ᵗ f
η⊣-nat f =
  eqᵗ (λ {t} x → cong₂ _,_ refl (map-nat f _ _) )

-- ε-⊣ is natural

ε⊣-nat : ∀ {A B τ} → (f : A →ᵗ B)
       → f ∘ᵗ ε⊣ ≡ᵗ ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f)
ε⊣-nat {A} {B} {τ} f =
  eqᵗ (λ { {t} (p , x) → map-nat f _ _ })

-- Triangle equations of the adjunction

ε⊣∘Fη≡id : ∀ {A τ} → ε⊣ {⟨ τ ⟩ᵒ A} ∘ᵗ ⟨ τ ⟩ᶠ (η⊣ {A}) ≡ᵗ idᵗ
ε⊣∘Fη≡id {A} {τ} =
  eqᵗ (λ {t} x →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (cong (λ p → monotone A p (proj₂ x)) (≤-irrelevant _ _))
          (monotone-refl A (proj₂ x))))))

Gε⊣∘η≡id : ∀ {A τ} → [ τ ]ᶠ (ε⊣ {A}) ∘ᵗ η⊣ {[ τ ]ᵒ A} ≡ᵗ idᵗ
Gε⊣∘η≡id {A} {τ} =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ _)
      (trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (monotone-refl A x))))

-- Interaction between η-⊣/ε-⊣ of the adjunction and η/ε of the modalities

η⊣≡ε⁻¹∘η : ∀ {A} → η⊣ {A} ≡ᵗ ε⁻¹ {⟨ 0 ⟩ᵒ A} ∘ᵗ η {A}
η⊣≡ε⁻¹∘η {A} =
  eqᵗ (λ {t} x →
    (cong₂ _,_
          (≤-irrelevant _ _)
          (cong (λ p → monotone A p x) (≤-irrelevant _ _))))

ε⊣≡ε∘η⁻¹ : ∀ {A} → ε⊣ {A} ≡ᵗ ε {A} ∘ᵗ η⁻¹ {[ 0 ]ᵒ A}
ε⊣≡ε∘η⁻¹ {A} =
  eqᵗ (λ { {t} (p , x) →
    cong (λ p → monotone A p x) (≤-irrelevant _ _) })

-- ...

