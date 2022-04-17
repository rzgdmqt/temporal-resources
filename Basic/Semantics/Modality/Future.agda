--------------------------------------------------------------------
-- Semantics of the future modality `[ t ] A` as a graded comonad --
--                                                                --
-- While `[ t ] A` is in fact a strong monoidal functor, then we  --
-- prefer to speak abour it in terms of the graded comonad view   --
-- of it due to the analogy with the comonad on types in Fitch    --
-- style modal lambda calculi (that this language is based on).   --
--------------------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Syntax.Language

open import Semantics.TSets

open import Util.Time

module Semantics.Modality.Future where

-- STRUCTURE

-- Functor

[_]ᵒ : Time → TSet → TSet
[ τ ]ᵒ A =
  tset
    (λ t' → carrier A (t' + τ))
    (λ p a → monotone A (+-mono-≤ p ≤-refl) a)
    (λ x → trans
             (cong (λ p → monotone A p x) (≤-irrelevant _ ≤-refl))
             (monotone-refl A x))
    (λ p q x → trans
                 (monotone-trans A _ _ x)
                 (cong
                   (λ r → monotone A r x)
                   (≤-irrelevant _ (+-mono-≤ (≤-trans p q) ≤-refl))))

[_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → [ τ ]ᵒ A →ᵗ [ τ ]ᵒ B
[ τ ]ᶠ (tset-map f) = tset-map f

-- Monotonicity for gradings

[]-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵗ [ τ₂ ]ᵒ A
[]-≤ {A} p =
  tset-map
    (λ a → monotone A (+-mono-≤ ≤-refl p) a)

-- Counit

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {A} =
  tset-map
    (λ {t} a → monotone A (≤-reflexive (+-identityʳ t)) a)

ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A
ε⁻¹ {A} =
  tset-map
    (λ {t} a → monotone A (≤-reflexive (sym (+-identityʳ t))) a)

-- Comultiplication

δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵗ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
δ {A} {τ₁} {τ₂} =
  tset-map
    (λ {t} a → monotone A (≤-reflexive (sym (+-assoc t τ₁ τ₂))) a)

δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵗ [ τ₁ + τ₂ ]ᵒ A
δ⁻¹ {A} {τ₁} {τ₂} =
  tset-map (λ {t} a → monotone A (≤-reflexive (+-assoc t τ₁ τ₂)) a)

-- Derived general unit map (a value now is
-- also available in at most τ time steps)

η-[] : ∀ {A τ} → A →ᵗ [ τ ]ᵒ A
η-[] {A} {τ} = []-≤ {A = A} z≤n ∘ᵗ ε⁻¹


-- PROPERTIES

-- [_]ᵒ commutes with ⇒ᵗ on constant domain

[]-⇒ᵗ : ∀ {A B τ} → [ τ ]ᵒ (ConstTSet A ⇒ᵗ B) →ᵗ ConstTSet A ⇒ᵗ [ τ ]ᵒ B
[]-⇒ᵗ {τ = τ} = tset-map (λ f p x → f  (+-monoˡ-≤ τ p) x)

⇒ᵗ-[] : ∀ {A B τ} → ConstTSet A ⇒ᵗ [ τ ]ᵒ B →ᵗ [ τ ]ᵒ (ConstTSet A ⇒ᵗ B)
⇒ᵗ-[] {B = B} {τ = τ} =
  tset-map (λ {t} f p x → monotone B p (f {t} ≤-refl x))

-- [_]ᵒ is functorial in the gradings

[]-≤-refl : ∀ {A τ} → []-≤ {A} (≤-refl {τ}) ≡ᵗ idᵗ
[]-≤-refl {A} x = 
  trans
    (cong (λ p → monotone A p x) (≤-irrelevant _ _))
    (monotone-refl A x)

[]-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
           → []-≤ {A} q ∘ᵗ []-≤ {A} p ≡ᵗ []-≤ {A} (≤-trans p q)
[]-≤-trans {A} p q x =
  trans
    (monotone-trans A _ _ x)
    (cong (λ r → monotone A r x) (≤-irrelevant _ _))

-- [_]ᵒ is strong monoidal

---- counit is an isomorphism

[]-ε∘ε⁻¹≡id : ∀ {A} → ε {A} ∘ᵗ ε⁻¹ ≡ᵗ idᵗ
[]-ε∘ε⁻¹≡id {A} x =
  trans
    (monotone-trans A _ _ x)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

[]-ε⁻¹∘ε≡id : ∀ {A} → ε⁻¹ {A} ∘ᵗ ε ≡ᵗ idᵗ
[]-ε⁻¹∘ε≡id {A} x =
  trans
    (monotone-trans A _ _ x)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

---- comultiplication is an isomorphism

[]-δ∘δ⁻¹≡id : ∀ {A τ₁ τ₂} → δ {A} {τ₁} {τ₂} ∘ᵗ δ⁻¹ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
[]-δ∘δ⁻¹≡id {A} {τ₁} {τ₂} x =
  trans
    (monotone-trans A _ _ x)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

[]-δ⁻¹∘δ≡id : ∀ {A τ₁ τ₂} → δ⁻¹ {A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
[]-δ⁻¹∘δ≡id {A} {τ₁} {τ₂} x =
  trans
    (monotone-trans A _ _ x)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))
