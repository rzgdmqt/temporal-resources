-------------------------------------------------------------------
-- Semantics of the past modality `Γ ⟨ t ⟩` as a strong monoidal --
-- functor indexed by (ℕ,≥). It is the analogue of the monadic   --
-- ◆-modality on contexts in Fitch-style modal lambda calculi.   --
--                                                               --
-- Note: While `Γ ⟨ t ⟩` is a strong monoidal functor, below we  --
-- use the terminology (unit, multiplication) of graded monads.  --
-------------------------------------------------------------------

module Semantics.Model.Examples.TSets.Modality.Past where

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

⟨_⟩ᵒ : Time → TSet → TSet
⟨ τ ⟩ᵒ (A) =
  tset
    (λ t' → τ ≤ t' × carrier A (t' ∸ τ))
    (λ p (q , x) → ≤-trans q p , monotone A (∸-mono p (≤-refl {τ})) x)
    (λ x → cong₂ _,_
             (≤-irrelevant _ _)
             (trans
               (cong (λ p → monotone A p (proj₂ x)) (≤-irrelevant _ _))
               (monotone-refl A (proj₂ x))))
    (λ p q x → cong₂ _,_
                 (≤-irrelevant _ _)
                 (trans
                   (monotone-trans A _ _ (proj₂ x))
                   (cong (λ r → monotone A r (proj₂ x)) (≤-irrelevant _ _))))

⟨_⟩ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → ⟨ τ ⟩ᵒ A →ᵗ ⟨ τ ⟩ᵒ B
⟨ τ ⟩ᶠ f =
  tset-map
    (λ { (p , x) → p , map-carrier f x })
    (λ { p (q , x) → cong (≤-trans q p ,_) (map-nat f _ x) })
 
-- (Contravariant) monotonicity for gradings

⟨⟩-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → ⟨ τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ A
⟨⟩-≤ {A} p =
  tset-map
    (λ { {t} (q , a) → ≤-trans p q , monotone A (∸-mono (≤-refl {t}) p) a })
    (λ { q (r , x) →
      cong₂ _,_
        (≤-irrelevant _ _)
        (trans
          (monotone-trans A _ _ x)
          (trans
            (cong (λ s → monotone A s x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ x)))) })

-- Unit (and its inverse)

η : ∀ {A} → A →ᵗ ⟨ 0 ⟩ᵒ A
η {A} =
  tset-map
    (λ x → z≤n , x)
    (λ p x → cong (z≤n ,_) (cong (λ q → monotone A q x) (≤-irrelevant _ _)))
 
η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵗ A
η⁻¹ {A} =
  tset-map
    (λ { (p , x) → x })
    (λ { p (q , x) → cong (λ r → monotone A r x) (≤-irrelevant _ _) })

-- Multiplication (and its inverse)

μ : ∀ {A τ₁ τ₂} → ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A) →ᵗ ⟨ τ₁ + τ₂ ⟩ᵒ A
μ {A} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , q , x) → n≤k⇒m≤k∸n⇒n+m≤k τ₁ τ₂ t p q ,
                           monotone A (≤-reflexive (n∸m∸k≡n∸m+k t τ₁ τ₂)) x })
    (λ { p (q , r , x) →
      cong₂ _,_
        (≤-irrelevant _ _)
        (trans
          (monotone-trans A _ _ x)
          (trans
            (cong (λ s → monotone A s x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ x)))) })
 
μ⁻¹ : ∀ {A τ₁ τ₂} → ⟨ τ₁ + τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A)
μ⁻¹ {A} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , a) → m+n≤o⇒m≤o τ₁ p ,
                       n+m≤k⇒m≤k∸n τ₁ τ₂ t p ,
                       monotone A (≤-reflexive (sym (n∸m∸k≡n∸m+k t τ₁ τ₂))) a })
    (λ { p (q , x) →
      cong₂ _,_
        (≤-irrelevant _ _)
        (cong₂ _,_
          (≤-irrelevant _ _)
          (trans
            (monotone-trans A _ _ x)
            (trans
              (cong (λ s → monotone A s x) (≤-irrelevant _ _))
              (sym (monotone-trans A _ _ x))))) })

-- Derived counit map (a value that was available
-- τ time steps in the past is also available now)

ε-⟨⟩ : ∀ {A τ} → ⟨ τ ⟩ᵒ A →ᵗ A
ε-⟨⟩ {A} {τ} =
  η⁻¹ ∘ᵗ ⟨⟩-≤ {A = A} z≤n


-- PROPERTIES

-- ⟨_⟩ is functorial

⟨⟩-idᵗ : ∀ {A τ} → ⟨ τ ⟩ᶠ (idᵗ {A = A}) ≡ᵗ idᵗ
⟨⟩-idᵗ =
  eqᵗ (λ {t} x → refl)
 
⟨⟩-∘ᵗ : ∀ {A B C τ} → (g : B →ᵗ C) → (f : A →ᵗ B)
      → ⟨ τ ⟩ᶠ (g ∘ᵗ f) ≡ᵗ ⟨ τ ⟩ᶠ g ∘ᵗ ⟨ τ ⟩ᶠ f
⟨⟩-∘ᵗ g f =
  eqᵗ (λ {t} x → refl)
 
⟨⟩-cong : ∀ {A B τ} {f g : A →ᵗ B}
        → f ≡ᵗ g
        → ⟨ τ ⟩ᶠ f ≡ᵗ ⟨ τ ⟩ᶠ g
⟨⟩-cong p = eqᵗ (λ x →
  cong₂ _,_
    refl
    (cong-app (fun-ext (prf p)) (proj₂ x)))

-- ⟨⟩-≤ is natural

⟨⟩-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B) → (p : τ₁ ≤ τ₂)
         → ⟨ τ₁ ⟩ᶠ f ∘ᵗ ⟨⟩-≤ {A = A} p ≡ᵗ ⟨⟩-≤ {A = B} p ∘ᵗ ⟨ τ₂ ⟩ᶠ f
⟨⟩-≤-nat f p =
  eqᵗ (λ { {t} (q , x) → cong (_ ,_) (map-nat f (∸-mono (≤-reflexive refl) p) x) })

-- ⟨_⟩ is functorial in the gradings

⟨⟩-≤-refl : ∀ {A τ} → ⟨⟩-≤ {A} (≤-refl {τ}) ≡ᵗ idᵗ
⟨⟩-≤-refl {A} =
  eqᵗ (λ { {t} (p , x) →
    (trans
      (cong₂ _,_
        (≤-irrelevant _ _)
        (cong (λ q → monotone A q x) (≤-irrelevant _ _)))
      (cong (_ ,_) (monotone-refl A x))) })

⟨⟩-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
           → ⟨⟩-≤ {A} p ∘ᵗ ⟨⟩-≤ {A} q ≡ᵗ ⟨⟩-≤ {A} (≤-trans p q)
⟨⟩-≤-trans {A} p q =
  eqᵗ (λ { {t} (r , x) →
    (trans
      (cong₂ _,_ refl (monotone-trans A _ _ x))
      (cong₂ _,_
        (≤-irrelevant _ _)
        (cong (λ q → monotone A q x) (≤-irrelevant _ _)))) })

⟨⟩-≤-cong : ∀ {A τ τ'} → (p q : τ ≤ τ')
          → ⟨⟩-≤ {A} p ≡ᵗ ⟨⟩-≤ {A} q
⟨⟩-≤-cong {A} p q =
  eqᵗ (λ { (r , x) →
    cong₂ _,_
      (≤-irrelevant _ _)
      (cong (λ r → monotone A r x) (≤-irrelevant _ _)) })

-- η and η⁻¹ are natural

⟨⟩-η-nat : ∀ {A B} → (f : A →ᵗ B)
         → ⟨ 0 ⟩ᶠ f ∘ᵗ η ≡ᵗ η ∘ᵗ f
⟨⟩-η-nat f =
  eqᵗ (λ {t} x → refl)
 
⟨⟩-η⁻¹-nat : ∀ {A B} → (f : A →ᵗ B)
           → f ∘ᵗ η⁻¹ ≡ᵗ η⁻¹ ∘ᵗ ⟨ 0 ⟩ᶠ f
⟨⟩-η⁻¹-nat f =
  eqᵗ (λ {t} x → refl)

-- μ and μ⁻¹ are natural

⟨⟩-μ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
           → ⟨ τ₁ + τ₂ ⟩ᶠ f ∘ᵗ μ {A} ≡ᵗ μ {B} ∘ᵗ ⟨ τ₁ ⟩ᶠ (⟨ τ₂ ⟩ᶠ f)
⟨⟩-μ-nat {τ₁ = τ₁} {τ₂ = τ₂} f =
  eqᵗ (λ { {t} (r , x) → (cong (_ ,_) (map-nat f _ _)) })      

⟨⟩-μ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
         → ⟨ τ₁ ⟩ᶠ (⟨ τ₂ ⟩ᶠ f) ∘ᵗ μ⁻¹ {A} ≡ᵗ μ⁻¹ {B} ∘ᵗ ⟨ τ₁ + τ₂ ⟩ᶠ f
⟨⟩-μ⁻¹-nat {τ₁ = τ₁} {τ₂ = τ₂} f =
  eqᵗ (λ { {t} (r , x) →
    (cong (m+n≤o⇒m≤o τ₁ r ,_)
      (cong (n+m≤k⇒m≤k∸n τ₁ τ₂ t r ,_)
        (map-nat f _ _))) })

⟨⟩-μ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
       → ⟨⟩-≤ {A} (+-mono-≤ p q) ∘ᵗ μ {A}
       ≡ᵗ μ {A} ∘ᵗ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ {A} q) ∘ᵗ ⟨⟩-≤ {⟨ τ₂' ⟩ᵒ A} p
⟨⟩-μ-≤ {A} p q =
  eqᵗ (λ { {t} (r , s , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (trans
            (cong (λ p → monotone A p x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ _)))
          (sym (monotone-trans A _ _ _)))))})

⟨⟩-μ-≤₁ : ∀ {A τ₁ τ₂ τ₁'} → (p : τ₁ ≤ τ₁')
        → ⟨⟩-≤ {A} (+-monoˡ-≤ τ₂ p) ∘ᵗ μ {A}
        ≡ᵗ μ {A} ∘ᵗ ⟨⟩-≤ {⟨ τ₂ ⟩ᵒ A} p
⟨⟩-μ-≤₁ {A} p =
  eqᵗ (λ { {t} (r , s , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (cong (λ p → monotone A p x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ _))))) })

⟨⟩-μ-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
        → ⟨⟩-≤ {A} (+-monoʳ-≤ τ₁ q) ∘ᵗ μ {A}
        ≡ᵗ μ {A} ∘ᵗ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ {A} q)
⟨⟩-μ-≤₂ {A} q =
  eqᵗ (λ { {t} (r , s , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (cong (λ p → monotone A p x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ _))))) })

⟨⟩-μ⁻¹-≤₂ : ∀ {A τ₁ τ₂ τ₂'} → (q : τ₂ ≤ τ₂')
          → μ⁻¹ {A} ∘ᵗ ⟨⟩-≤ {A} (+-monoʳ-≤ τ₁ q)
         ≡ᵗ ⟨ τ₁ ⟩ᶠ (⟨⟩-≤ {A} q) ∘ᵗ μ⁻¹ {A}
⟨⟩-μ⁻¹-≤₂ {A} q =
  eqᵗ (λ { {t} (r , x) → 
    (cong₂ _,_
      (≤-irrelevant _ _)
      (cong₂ _,_
        (≤-irrelevant _ _)
        (trans
          (monotone-trans A _ _ _)
          (trans
            (cong (λ p → monotone A p x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ _)))))) })

-- η is invertible

⟨⟩-η∘η⁻¹≡id : ∀ {A} → η {A} ∘ᵗ η⁻¹ ≡ᵗ idᵗ
⟨⟩-η∘η⁻¹≡id {A} =
  eqᵗ (λ { {t} (p , x) → cong₂ _,_ (≤-irrelevant _ _) refl })      
 
⟨⟩-η⁻¹∘η≡id : ∀ {A} → η⁻¹ {A} ∘ᵗ η ≡ᵗ idᵗ
⟨⟩-η⁻¹∘η≡id {A} =
  eqᵗ (λ {t} x → refl)

-- μ is invertible

⟨⟩-μ∘μ⁻¹≡id : ∀ {A τ₁ τ₂}
            → μ {A} {τ₁} {τ₂} ∘ᵗ μ⁻¹ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
⟨⟩-μ∘μ⁻¹≡id {A} {τ₁} {τ₂} =
  eqᵗ (λ { {t} (p , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (monotone-refl A _)))) })

⟨⟩-μ⁻¹∘μ≡id : ∀ {A τ₁ τ₂}
            → μ⁻¹ {A} {τ₁} {τ₂} ∘ᵗ μ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
⟨⟩-μ⁻¹∘μ≡id {A} {τ₁} {τ₂} =
  eqᵗ (λ { {t} (p , q , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (cong₂ _,_
        (≤-irrelevant _ _)
        (trans
          (monotone-trans A _ _ _)
          (trans
            (cong (λ q → monotone A q x) (≤-irrelevant _ _))
            (monotone-refl A _))))) })

-- Graded monad laws

⟨⟩-μ∘η≡id : ∀ {A τ} → μ {A} {0} {τ} ∘ᵗ η {⟨ τ ⟩ᵒ A} ≡ᵗ idᵗ
⟨⟩-μ∘η≡id {A} =
  eqᵗ (λ { {t} (p , x) →
    (cong (p ,_)
      (trans
        (cong (λ q → monotone A q x) (≤-irrelevant _ _))
        (monotone-refl A _))) })

⟨⟩-μ∘Tη≡id : ∀ {A τ}
          → μ {A} {τ} {0} ∘ᵗ ⟨ τ ⟩ᶠ (η {A})
          ≡ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-identityʳ τ))
⟨⟩-μ∘Tη≡id {A} =
  eqᵗ (λ { {t} (p , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (cong (λ q → monotone A q x) (≤-irrelevant _ _))) })

⟨⟩-μ∘μ≡≤∘μ∘Tμ : ∀ {A τ₁ τ₂ τ₃}
              → μ {A} {τ₁ + τ₂} {τ₃} ∘ᵗ μ {⟨ τ₃ ⟩ᵒ A} {τ₁} {τ₂}
              ≡ᵗ ⟨⟩-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃)) ∘ᵗ μ {A} {τ₁} {τ₂ + τ₃} ∘ᵗ ⟨ τ₁ ⟩ᶠ (μ {A} {τ₂} {τ₃})
              
⟨⟩-μ∘μ≡≤∘μ∘Tμ {A} {τ₁} {τ₂} {τ₃} =
  eqᵗ (λ { {t} (p , q , r , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (trans
        (monotone-trans A _ _ _)
        (trans
          (trans
            (cong (λ s → monotone A s x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ _)))
          (sym (monotone-trans A _ _ _))))) })

-- Graded monad laws (for inverses)

⟨⟩-Tη⁻¹∘ᵗμ⁻¹≡id : ∀ {A τ}
    →  ⟨ τ ⟩ᶠ (η⁻¹ {A}) ∘ᵗ μ⁻¹ {A} {τ} {0}
    ≡ᵗ ⟨⟩-≤ {A} (≤-reflexive (sym (+-identityʳ _)))
⟨⟩-Tη⁻¹∘ᵗμ⁻¹≡id {A} =
  eqᵗ (λ { {t} (p , x) →
    (cong₂ _,_
      (≤-irrelevant _ _)
      (cong (λ p → monotone A p x) (≤-irrelevant _ _)))})

