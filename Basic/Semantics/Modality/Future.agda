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
    (λ p x → monotone A (+-mono-≤ p ≤-refl) x)
    (λ x → trans
             (cong (λ p → monotone A p x) (≤-irrelevant _ ≤-refl))
             (monotone-refl A x))
    (λ p q x → trans
                 (monotone-trans A _ _ x)
                 (cong
                   (λ r → monotone A r x)
                   (≤-irrelevant _ (+-mono-≤ (≤-trans p q) ≤-refl))))

[_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → [ τ ]ᵒ A →ᵗ [ τ ]ᵒ B
[ τ ]ᶠ f =
  tset-map
    (map-carrier f)
    (λ p x → map-nat f (+-mono-≤ p ≤-refl) x)

-- Monotonicity for gradings

[]-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵗ [ τ₂ ]ᵒ A
[]-≤ {A} p =
  tset-map
    (λ x → monotone A (+-mono-≤ ≤-refl p) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

-- Counit

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {A} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (+-identityʳ t)) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A
ε⁻¹ {A} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (sym (+-identityʳ t))) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

-- Comultiplication

δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵗ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
δ {A} {τ₁} {τ₂} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (sym (+-assoc t τ₁ τ₂))) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵗ [ τ₁ + τ₂ ]ᵒ A
δ⁻¹ {A} {τ₁} {τ₂} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (+-assoc t τ₁ τ₂)) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

-- Derived general unit map (a value now is
-- also available in at most τ time steps)

η-[] : ∀ {A τ} → A →ᵗ [ τ ]ᵒ A
η-[] {A} {τ} = []-≤ {A = A} z≤n ∘ᵗ ε⁻¹


-- PROPERTIES

-- [_] is functorial

[]-id : ∀ {A τ} → [ τ ]ᶠ (idᵗ {A = A}) ≡ᵗ idᵗ
[]-id x = refl

[]-∘ : ∀ {A B C τ} → (f : A →ᵗ B) → (g : B →ᵗ C)
     → [ τ ]ᶠ (g ∘ᵗ f) ≡ᵗ [ τ ]ᶠ g ∘ᵗ [ τ ]ᶠ f
[]-∘ f g x = refl

-- []-≤ is natural

[]-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B) → (p : τ₁ ≤ τ₂)
         → [ τ₂ ]ᶠ f ∘ᵗ []-≤ {A = A} p ≡ᵗ []-≤ {A = B} p ∘ᵗ [ τ₁ ]ᶠ f
[]-≤-nat f p x = map-nat f (+-mono-≤ (≤-reflexive refl) p) x

-- [_] is functorial in the gradings

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

-- ε and ε⁻¹ are natural

[]-ε-nat : ∀ {A B} → (f : A →ᵗ B)
         → f ∘ᵗ ε ≡ᵗ ε ∘ᵗ [ 0 ]ᶠ f
[]-ε-nat f {t} x = map-nat f (≤-reflexive (+-identityʳ t)) x

[]-ε⁻¹-nat : ∀ {A B} → (f : A →ᵗ B)
           → [ 0 ]ᶠ f ∘ᵗ ε⁻¹ ≡ᵗ ε⁻¹ ∘ᵗ f
[]-ε⁻¹-nat f {t} x = map-nat f (≤-reflexive (sym (+-identityʳ t))) x

-- δ and δ⁻¹ are natural

[]-δ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
         → [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f) ∘ᵗ δ {A} ≡ᵗ δ {B} ∘ᵗ [ τ₁ + τ₂ ]ᶠ f
[]-δ-nat {τ₁ = τ₁} {τ₂ = τ₂} f {t} x =
  map-nat f (≤-reflexive (sym (+-assoc t τ₁ τ₂))) x

[]-δ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
           → [ τ₁ + τ₂ ]ᶠ f ∘ᵗ δ⁻¹ {A} ≡ᵗ δ⁻¹ {B} ∘ᵗ [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f)
[]-δ⁻¹-nat {τ₁ = τ₁} {τ₂ = τ₂} f {t} x =
  map-nat f (≤-reflexive (+-assoc t τ₁ τ₂)) x

[]-δ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
       → [ τ₁' ]ᶠ ([]-≤ {A} q) ∘ᵗ []-≤ {[ τ₂ ]ᵒ A} p ∘ᵗ δ {A = A}
       ≡ᵗ δ {A} ∘ᵗ []-≤ {A} (+-mono-≤ p q)
[]-δ-≤ {A} p q x =
  trans
    (monotone-trans A _ _ _)
    (trans
      (monotone-trans A _ _ _)
      (trans
        (cong (λ r → monotone A r x) (≤-irrelevant _ _))
        (sym (monotone-trans A _ _ _))))

-- [_] is strong monoidal

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

-- Graded comonad laws

[]-ε∘δ≡id : ∀ {A τ} → ε ∘ᵗ δ {A} {0} {τ} ≡ᵗ idᵗ
[]-ε∘δ≡id {A} {τ} x =
  trans
    (monotone-trans A _ _ x)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

[]-Dε∘δ≡≤ : ∀ {A τ}
          → [ τ ]ᶠ (ε {A}) ∘ᵗ δ {A} {τ} {0}
          ≡ᵗ []-≤ {A} (≤-reflexive (+-identityʳ τ))
[]-Dε∘δ≡≤ {A} x =
  trans
    (monotone-trans A _ _ x)
    (cong (λ p → monotone A p x) (≤-irrelevant _ _))
             
[]-δ∘δ≡Dδ∘δ∘≤ : ∀ {A τ₁ τ₂ τ₃}
              → δ {[ τ₃ ]ᵒ A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁ + τ₂} {τ₃}
              ≡ᵗ    [ τ₁ ]ᶠ (δ {A} {τ₂} {τ₃}) ∘ᵗ δ {A} {τ₁} {τ₂ + τ₃}
                 ∘ᵗ []-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃))
[]-δ∘δ≡Dδ∘δ∘≤ {A} x =
  trans
    (monotone-trans A _ _ x)
    (trans
      (trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (sym (monotone-trans A _ _ _)))
      (sym (monotone-trans A _ _ _)))
