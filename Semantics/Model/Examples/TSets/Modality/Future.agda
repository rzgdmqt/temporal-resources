------------------------------------------------------------------------
-- Semantics of the future modality `[ t ] A` as a strong monoidal    --
-- functor indexed by (ℕ,≤). It is the analogue of the comonadic      --
-- □-modality on types/formulae in Fitch-style modal lambda calculi.  --
--                                                                    --
-- Note: While `[ t ] A` is a strong monoidal functor, then below we  --
-- use the terminology (counit, comultiplication) of graded comonads. --
------------------------------------------------------------------------

module Semantics.Model.Examples.TSets.Modality.Future where

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

open import Syntax.Language

open import Semantics.Model.Examples.TSets.TSets

open import Util.Equality
open import Util.Time

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

-- Counit and its inverse

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

-- Comultiplication and its inverse

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

[]-idᵗ : ∀ {A τ} → [ τ ]ᶠ (idᵗ {A = A}) ≡ᵗ idᵗ
[]-idᵗ =
  eqᵗ (λ {t} x → refl)
 
[]-∘ᵗ : ∀ {A B C τ} → (f : A →ᵗ B) → (g : B →ᵗ C)
      → [ τ ]ᶠ (g ∘ᵗ f) ≡ᵗ [ τ ]ᶠ g ∘ᵗ [ τ ]ᶠ f
[]-∘ᵗ {τ = τ} f g =
  eqᵗ (λ {t} x → refl)

-- []-≤ is natural

[]-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B) → (p : τ₁ ≤ τ₂)
         → [ τ₂ ]ᶠ f ∘ᵗ []-≤ {A = A} p ≡ᵗ []-≤ {A = B} p ∘ᵗ [ τ₁ ]ᶠ f
[]-≤-nat {A} {B} {τ₁ = τ₁} {τ₂ = τ₂} f p = eqᵗ (λ {t} x →
  (map-nat f (+-mono-≤ (≤-reflexive refl) p) x))

-- [_] is functorial in the gradings

[]-≤-refl : ∀ {A τ} → []-≤ {A} (≤-refl {τ}) ≡ᵗ idᵗ
[]-≤-refl {A} =
  eqᵗ (λ {t} x →
    trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

[]-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
           → []-≤ {A} q ∘ᵗ []-≤ {A} p ≡ᵗ []-≤ {A} (≤-trans p q)
[]-≤-trans {A} p q =
  eqᵗ (λ {t} x →
    trans
      (monotone-trans A _ _ x)
      (cong (λ r → monotone A r x) (≤-irrelevant _ _)))

-- ε and ε⁻¹ are natural

[]-ε-nat : ∀ {A B} → (f : A →ᵗ B)
         → f ∘ᵗ ε ≡ᵗ ε ∘ᵗ [ 0 ]ᶠ f
[]-ε-nat f =
  eqᵗ (λ {t} x → map-nat f (≤-reflexive (+-identityʳ t)) x)

[]-ε⁻¹-nat : ∀ {A B} → (f : A →ᵗ B)
           → [ 0 ]ᶠ f ∘ᵗ ε⁻¹ ≡ᵗ ε⁻¹ ∘ᵗ f
[]-ε⁻¹-nat f =
  eqᵗ (λ {t} x → map-nat f (≤-reflexive (sym (+-identityʳ t))) x)

-- δ and δ⁻¹ is natural

[]-δ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
         → [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f) ∘ᵗ δ {A} ≡ᵗ δ {B} ∘ᵗ [ τ₁ + τ₂ ]ᶠ f
[]-δ-nat {τ₁ = τ₁} {τ₂ = τ₂} f =
  eqᵗ (λ {t} x → map-nat f (≤-reflexive (sym (+-assoc t τ₁ τ₂))) x)

[]-δ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
           → [ τ₁ + τ₂ ]ᶠ f ∘ᵗ δ⁻¹ {A} ≡ᵗ δ⁻¹ {B} ∘ᵗ [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f)
[]-δ⁻¹-nat {τ₁ = τ₁} {τ₂ = τ₂} f =
  eqᵗ (λ {t} x → map-nat f (≤-reflexive (+-assoc t τ₁ τ₂)) x)

[]-δ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
       → [ τ₁' ]ᶠ ([]-≤ {A} q) ∘ᵗ []-≤ {[ τ₂ ]ᵒ A} p ∘ᵗ δ {A = A}
      ≡ᵗ δ {A} ∘ᵗ []-≤ {A} (+-mono-≤ p q)
[]-δ-≤ {A} {τ₁' = τ₁'} p q =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (cong (λ r → monotone A r x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ _))))))

-- ε is invertible

[]-ε∘ε⁻¹≡id : ∀ {A} → ε {A} ∘ᵗ ε⁻¹ ≡ᵗ idᵗ
[]-ε∘ε⁻¹≡id {A} =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ x)
      (trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (monotone-refl A x))))

[]-ε⁻¹∘ε≡id : ∀ {A} → ε⁻¹ {A} ∘ᵗ ε ≡ᵗ idᵗ
[]-ε⁻¹∘ε≡id {A} =
  eqᵗ (λ {t} x →
    (trans
          (monotone-trans A _ _ x)
          (trans
            (cong (λ p → monotone A p x) (≤-irrelevant _ _))
            (monotone-refl A x))))

-- δ is invertible

[]-δ∘δ⁻¹≡id : ∀ {A τ₁ τ₂} → δ {A} {τ₁} {τ₂} ∘ᵗ δ⁻¹ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
[]-δ∘δ⁻¹≡id {A} {τ₁} {τ₂} =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ x)
      (trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (monotone-refl A x))))

[]-δ⁻¹∘δ≡id : ∀ {A τ₁ τ₂} → δ⁻¹ {A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
[]-δ⁻¹∘δ≡id {A} {τ₁} {τ₂} =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ x)
      (trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (monotone-refl A x))))

-- Graded comonad laws

[]-ε∘δ≡id : ∀ {A τ} → ε ∘ᵗ δ {A} {0} {τ} ≡ᵗ idᵗ
[]-ε∘δ≡id {A} {τ} =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ x)
      (trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (monotone-refl A x))))
[]-Dε∘δ≡id : ∀ {A τ}
          → [ τ ]ᶠ (ε {A}) ∘ᵗ δ {A} {τ} {0}
          ≡ᵗ []-≤ {A} (≤-reflexive (+-identityʳ τ))
[]-Dε∘δ≡id {A} =
  eqᵗ (λ {t} x →
   (trans
     (monotone-trans A _ _ x)
     (cong (λ p → monotone A p x) (≤-irrelevant _ _))))

[]-δ∘δ≡Dδ∘δ : ∀ {A τ₁ τ₂ τ₃}
              → δ {[ τ₃ ]ᵒ A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁ + τ₂} {τ₃}
              ≡ᵗ    [ τ₁ ]ᶠ (δ {A} {τ₂} {τ₃}) ∘ᵗ δ {A} {τ₁} {τ₂ + τ₃}
                 ∘ᵗ []-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃))
[]-δ∘δ≡Dδ∘δ {A} {τ₁} {τ₂} {τ₃} =
  eqᵗ (λ {t} x →
    (trans
      (monotone-trans A _ _ x)
      (trans
        (trans
          (cong (λ p → monotone A p x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ _)))
        (sym (monotone-trans A _ _ _)))))

-- [_]ᵒ is monoidal (with respect to ×ᵗ)

[]-monoidal : ∀ {A B τ}
            → [ τ ]ᵒ A ×ᵗ [ τ ]ᵒ B →ᵗ [ τ ]ᵒ (A ×ᵗ B)
[]-monoidal {A} {B} {τ} =
  tset-map
    (λ xy → xy)
    (λ p xy → refl)


-- Packaging the future modality up in the model

open import Semantics.Model.Modality.Future

TSetFut : Future TSetCat
TSetFut = record
  { [_]ᵒ        = [_]ᵒ
  ; [_]ᶠ        = [_]ᶠ
  ; []-≤        = λ {A} → []-≤ {A}
  ; ε           = ε
  ; ε⁻¹         = ε⁻¹
  ; δ           = λ {A} → δ {A}
  ; δ⁻¹         = λ {A} → δ⁻¹ {A}
  ; []-idᵐ      = λ {A} → ≡ᵗ-≡ ([]-idᵗ {A})
  ; []-∘ᵐ       = λ f g → ≡ᵗ-≡ ([]-∘ᵗ f g)
  ; []-≤-nat    = λ f p → ≡ᵗ-≡ ([]-≤-nat f p)
  ; []-≤-refl   = λ {A} → ≡ᵗ-≡ ([]-≤-refl {A})
  ; []-≤-trans  = λ {A} p q → ≡ᵗ-≡ ([]-≤-trans {A} p q)
  ; []-ε-nat    = λ f → ≡ᵗ-≡ ([]-ε-nat f)
  ; []-ε⁻¹-nat  = λ f → ≡ᵗ-≡ ([]-ε⁻¹-nat f)
  ; []-δ-nat    = λ f → ≡ᵗ-≡ ([]-δ-nat f)
  ; []-δ⁻¹-nat  = λ f → ≡ᵗ-≡ ([]-δ⁻¹-nat f)
  ; []-δ-≤      = λ {A} p q → ≡ᵗ-≡ ([]-δ-≤ {A} p q)
  ; []-ε∘ε⁻¹≡id = λ {A} → ≡ᵗ-≡ ([]-ε∘ε⁻¹≡id {A})
  ; []-ε⁻¹∘ε≡id = λ {A} → ≡ᵗ-≡ ([]-ε⁻¹∘ε≡id {A})
  ; []-δ∘δ⁻¹≡id = λ {A} → ≡ᵗ-≡ ([]-δ∘δ⁻¹≡id {A})
  ; []-δ⁻¹∘δ≡id = λ {A} → ≡ᵗ-≡ ([]-δ⁻¹∘δ≡id {A})
  ; []-ε∘δ≡id   = λ {A} → ≡ᵗ-≡ ([]-ε∘δ≡id {A})
  ; []-Dε∘δ≡id  = λ {A} → ≡ᵗ-≡ ([]-Dε∘δ≡id {A})
  ; []-δ∘δ≡Dδ∘δ = λ {A} → ≡ᵗ-≡ ([]-δ∘δ≡Dδ∘δ {A})
  ; []-monoidal = λ {A} {B} → []-monoidal {A} {B}
  }

