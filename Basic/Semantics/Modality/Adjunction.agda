---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

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

open import Semantics.Modality.Future
open import Semantics.Modality.Past

open import Util.Time

module Semantics.Modality.Adjunction where

-- STRUCTURE

-- Unit of the adjunction

η⊣ : ∀ {A τ} → A →ᵗ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
η⊣ {A} {τ} =
  tset-map
    (λ {t'} a →
      m≤n+m τ t' ,
      monotone A (≤-reflexive (sym (m+n∸n≡m t' τ))) a)

-- Counit of the adjunction

ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵗ A
ε⊣ {A} {τ} =
  tset-map
    (λ { {t'} (p , a) → monotone A (n≤m⇒m∸n+n≤m τ t' p) a })


-- PROPERTIES

-- Triangle equations of the adjunction

⊣-ε∘Fη≡id : ∀ {A τ} → ε⊣ {⟨ τ ⟩ᵒ A} ∘ᵗ ⟨ τ ⟩ᶠ (η⊣ {A}) ≡ᵗ idᵗ
⊣-ε∘Fη≡id {A} {τ} x =
  cong₂ _,_
    (≤-irrelevant _ _)
    (trans
      (monotone-trans A _ _ _)
      (trans
        (cong (λ p → monotone A p (proj₂ x)) (≤-irrelevant _ _))
        (monotone-refl A (proj₂ x))))

⊣-Gε∘η≡id : ∀ {A τ} → [ τ ]ᶠ (ε⊣ {A}) ∘ᵗ η⊣ {[ τ ]ᵒ A} ≡ᵗ idᵗ
⊣-Gε∘η≡id {A} {τ} x =
  trans
    (monotone-trans A _ _ _)
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x))

-- ...









{-

-- ALTERNATIVE CHARACTERISATION using modules-comodules

-- Auxiliary lemmas

m≤n⇒n∸m+k≤n+k∸m : (n m k : ℕ)
                → m ≤ n → n ∸ m + k ≤ n + (k ∸ m)
m≤n⇒n∸m+k≤n+k∸m zero zero zero p = p
m≤n⇒n∸m+k≤n+k∸m zero zero (suc k) p =
  s≤s (m≤n⇒n∸m+k≤n+k∸m zero zero k p)
m≤n⇒n∸m+k≤n+k∸m (suc n) zero zero p =
  s≤s (m≤n⇒n∸m+k≤n+k∸m n zero zero z≤n)
m≤n⇒n∸m+k≤n+k∸m (suc n) zero (suc k) p =
  s≤s (m≤n⇒n∸m+k≤n+k∸m n zero (suc k) z≤n)
m≤n⇒n∸m+k≤n+k∸m (suc n) (suc m) zero (s≤s p) =
  ≤-trans
    (≤-reflexive (+-identityʳ (n ∸ m)))
    (≤-trans
      (≤-trans
        (m∸n≤m n m)
        (n≤1+n n))
      (≤-reflexive (cong suc (sym (+-identityʳ n)))))
m≤n⇒n∸m+k≤n+k∸m (suc n) (suc m) (suc k) (s≤s p) =
  ≤-trans
    (≤-reflexive (+-suc (n ∸ m) k))
    (+-monoʳ-≤ 1 (m≤n⇒n∸m+k≤n+k∸m n m k p))

m∸n≤k⇒k∸m∸n≤k+n∸m : (m n k : ℕ)
                  → m ∸ n ≤ k → k ∸ (m ∸ n) ≤ k + n ∸ m
m∸n≤k⇒k∸m∸n≤k+n∸m zero    zero    zero    p = p
m∸n≤k⇒k∸m∸n≤k+n∸m zero    zero    (suc k) p =
  s≤s (m∸n≤k⇒k∸m∸n≤k+n∸m zero zero k z≤n)
m∸n≤k⇒k∸m∸n≤k+n∸m zero    (suc n) zero    p = z≤n
m∸n≤k⇒k∸m∸n≤k+n∸m zero    (suc n) (suc k) p =
  s≤s (m∸n≤k⇒k∸m∸n≤k+n∸m zero (suc n) k z≤n)
m∸n≤k⇒k∸m∸n≤k+n∸m (suc m) zero    (suc k) p =
  ≤-reflexive (cong (_∸ m) (sym (+-identityʳ k)))
m∸n≤k⇒k∸m∸n≤k+n∸m (suc m) (suc n) zero    p =
  m∸n≤k⇒k∸m∸n≤k+n∸m m n zero p
m∸n≤k⇒k∸m∸n≤k+n∸m (suc m) (suc n) (suc k) p =
  ≤-trans
    (m∸n≤k⇒k∸m∸n≤k+n∸m m n (suc k) p)
    (≤-reflexive (cong (_∸ m) (sym (+-suc k n))))

m≤m∸n+n : (n m : ℕ) → m ≤ m ∸ n + n
m≤m∸n+n zero zero = z≤n
m≤m∸n+n zero (suc m) = s≤s (m≤m∸n+n zero m)
m≤m∸n+n (suc n) zero = z≤n
m≤m∸n+n (suc n) (suc m) =
  ≤-trans
    (+-monoʳ-≤ 1 (m≤m∸n+n n m))
    (≤-reflexive (sym (+-suc (m ∸ n) n)))

-- ⟨_⟩ is a [_]-comodule

α :  ∀ {A τ τ'} → ⟨ τ' ∸ τ ⟩ᵒ A →ᵗ [ τ ]ᵒ (⟨ τ' ⟩ᵒ A)
α {A} {τ} {τ'} =
  tset-map
    (λ { {t} (p , x) →
      ≤-trans
        (m≤m∸n+n τ τ')
        (+-monoˡ-≤ τ p) ,
      monotone A (m∸n≤k⇒k∸m∸n≤k+n∸m τ' τ t p) x })

-- [_] is a ⟨_⟩-module

β : ∀ {A τ τ'} → ⟨ τ' ⟩ᵒ ([ τ ]ᵒ A) →ᵗ [ τ ∸ τ' ]ᵒ A
β {A} {τ} {τ'} =
  tset-map
    (λ { {t} (p , x) →
      monotone A (m≤n⇒n∸m+k≤n+k∸m t τ' τ p) x })

-}
