----------------------------------------------
-- Time-indexed sets and modalities on them --
----------------------------------------------

open import Function

open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

module TSets where

-- Time steps (using natural numbers)

Time : Set
Time = ℕ

-- Auxiliary lemmas

n∸m∸k≡n∸m+k : (n m k : ℕ) → n ∸ m ∸ k ≡ n ∸ (m + k)
n∸m∸k≡n∸m+k zero    zero    k       = refl
n∸m∸k≡n∸m+k zero    (suc m) zero    = refl
n∸m∸k≡n∸m+k zero    (suc m) (suc k) = refl
n∸m∸k≡n∸m+k (suc n) zero    k       = refl
n∸m∸k≡n∸m+k (suc n) (suc m) k       = n∸m∸k≡n∸m+k n m k

n≤k⇒m≤k∸n⇒n+m≤k : (n m k : ℕ) → n ≤ k → m ≤ k ∸ n → n + m ≤ k
n≤k⇒m≤k∸n⇒n+m≤k zero m k z≤n q = q
n≤k⇒m≤k∸n⇒n+m≤k (suc n) m (suc k) (s≤s p) q =
  +-monoʳ-≤ 1 (n≤k⇒m≤k∸n⇒n+m≤k n m k p q)

n≤m⇒m∸n+n≤m : (n m : ℕ) → n ≤ m → m ∸ n + n ≤ m
n≤m⇒m∸n+n≤m zero m z≤n =
  ≤-reflexive (+-identityʳ m)
n≤m⇒m∸n+n≤m (suc n) (suc m) (s≤s p) =
  ≤-trans
    (≤-reflexive (+-suc (m ∸ n) n))
    (+-monoʳ-≤ 1 (n≤m⇒m∸n+n≤m n m p))

n+m≤k⇒m≤k∸n : (n m k : ℕ) → n + m ≤ k → m ≤ k ∸ n
n+m≤k⇒m≤k∸n zero    m       k       p       = p
n+m≤k⇒m≤k∸n (suc n) zero    k       p       = z≤n
n+m≤k⇒m≤k∸n (suc n) (suc m) (suc k) (s≤s p) = n+m≤k⇒m≤k∸n n (suc m) k p

-- Time-indexed sets

record TSet : Set₁ where
  constructor
    tset
  field
    carrier  : Time → Set
    monotone : ∀ {t t'} → t ≤ t' → carrier t → carrier t'

    -- TODO: also include the functor laws for refl-id and trans-∘

open TSet

record _→ᵗ_ (A B : TSet) : Set where
  constructor
    tset-map
  field
    map-carrier : ∀ {t} → carrier A t → carrier B t

    -- TODO: also include naturality law

open _→ᵗ_

-- Semantics of the type modality `[ t ] A` as a graded comonad

[_]ᵒ : Time → TSet → TSet
[ t ]ᵒ (tset A Af) =
  tset
    (λ t' → A (t' + t))
    (λ p a → Af (+-mono-≤ p ≤-refl) a)

[_]ᶠ : ∀ {A B} → (t : Time) → A →ᵗ B → [ t ]ᵒ A →ᵗ [ t ]ᵒ B
[ t ]ᶠ (tset-map f) = tset-map f

[_]-≤ : ∀ {A t₁ t₂} → t₁ ≤ t₂ → [ t₁ ]ᵒ A →ᵗ [ t₂ ]ᵒ A
[_]-≤ {tset A Af} p =
  tset-map
    (λ a → Af (+-mono-≤ ≤-refl p) a)

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {tset A Af} =
  tset-map
    (λ {t} a → Af (≤-reflexive (+-identityʳ t)) a)

ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A
ε⁻¹ {tset A Af} =
  tset-map
    (λ {t} a → Af (≤-reflexive (sym (+-identityʳ t))) a)

δ : ∀ {A t₁ t₂} → [ t₁ + t₂ ]ᵒ A →ᵗ [ t₁ ]ᵒ ([ t₂ ]ᵒ A)
δ {tset A Af} {t₁} {t₂} =
  tset-map
    (λ {t} a → Af (≤-reflexive (sym (+-assoc t t₁ t₂))) a)

δ⁻¹ : ∀ {A t₁ t₂} → [ t₁ ]ᵒ ([ t₂ ]ᵒ A) →ᵗ [ t₁ + t₂ ]ᵒ A
δ⁻¹ {tset A Af} {t₁} {t₂} =
  tset-map (λ {t} a → Af (≤-reflexive (+-assoc t t₁ t₂)) a)

-- Semantics of the context modality `Γ ⟨ t ⟩` as a graded monad

⟨_⟩ᵒ : Time → TSet → TSet
⟨ t ⟩ᵒ (tset A Af) =
  tset
    (λ t' → t ≤ t' × A (t' ∸ t))
    (λ p (q , a) → ≤-trans q p , Af (∸-mono p (≤-refl {t})) a)

⟨_⟩ᶠ : ∀ {A B} → (t : Time) → A →ᵗ B → ⟨ t ⟩ᵒ A →ᵗ ⟨ t ⟩ᵒ B
⟨ t ⟩ᶠ (tset-map f) =
  tset-map
    (λ { (p , a) → p , f a })

⟨_⟩-≤ : ∀ {A t₁ t₂} → t₁ ≤ t₂ → ⟨ t₂ ⟩ᵒ A →ᵗ ⟨ t₁ ⟩ᵒ A
⟨_⟩-≤ {tset A Af} p =
  tset-map
    (λ { {t} (q , a) → ≤-trans p q , Af (∸-mono (≤-refl {t}) p) a })

η : ∀ {A} → A →ᵗ ⟨ 0 ⟩ᵒ A
η =
  tset-map
    (λ a → z≤n , a)

η⁻¹ : ∀ {A} → ⟨ 0 ⟩ᵒ A →ᵗ A
η⁻¹ =
  tset-map
    (λ { (p , a) → a })

μ : ∀ {A t₁ t₂} → ⟨ t₁ ⟩ᵒ (⟨ t₂ ⟩ᵒ A) →ᵗ ⟨ t₁ + t₂ ⟩ᵒ A
μ {tset A Af} {t₁} {t₂} =
  tset-map
    (λ { {t} (p , q , a) → n≤k⇒m≤k∸n⇒n+m≤k t₁ t₂ t p q ,
                           Af (≤-reflexive (n∸m∸k≡n∸m+k t t₁ t₂)) a })

μ⁻¹ : ∀ {A t₁ t₂} → ⟨ t₁ + t₂ ⟩ᵒ A →ᵗ ⟨ t₁ ⟩ᵒ (⟨ t₂ ⟩ᵒ A)
μ⁻¹ {tset A Af} {t₁} {t₂} =
  tset-map
    (λ { {t} (p , a) → m+n≤o⇒m≤o t₁ p ,
                       n+m≤k⇒m≤k∸n t₁ t₂ t p ,
                       Af (≤-reflexive (sym (n∸m∸k≡n∸m+k t t₁ t₂))) a })

-- Adjunction between the graded monad and comonad

η⊣ : ∀ {A t} → A →ᵗ [ t ]ᵒ (⟨ t ⟩ᵒ A)
η⊣ {tset A Af} {t} =
  tset-map
    (λ {t'} a → m≤n+m t t' , Af (≤-reflexive (sym (m+n∸n≡m t' t))) a)

ε⊣ : ∀ {A t} → ⟨ t ⟩ᵒ ([ t ]ᵒ A) →ᵗ A
ε⊣ {tset A Af} {t} =
  tset-map
    (λ { {t'} (p , a) → Af (n≤m⇒m∸n+n≤m t t' p) a })

-- ...
