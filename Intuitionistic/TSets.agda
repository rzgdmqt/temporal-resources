----------------------------------------------
-- Time-indexed sets and modalities on them --
----------------------------------------------

open import Function

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Language

module TSets where

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

≤-split-+ : ∀ {n n' m k} → n ≡ m + k → n ≤ n' → 0 < m → Σ[ k' ∈ ℕ ] (n' ≡ m + k' × k ≤ k')
≤-split-+ {n' = n'} {m = m} p z≤n r
  rewrite m+n≡0⇒m≡0 m (sym p) | m+n≡0⇒n≡0 m (sym p) = n' , refl , z≤n
≤-split-+ {n = suc n} {n' = n'} {m = suc m} {k = k} p (s≤s q) (s≤s r) = {!!}
--with ≤-split-+ {!!} q (s≤s r)
--... | p' , q' , r' = {!!} , {!!} , {!!}

-- Time-indexed sets (covariant presheaves indexed by `(ℕ,≤)`)

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

infix 20 _→ᵗ_

open _→ᵗ_

-- Product, sum, exponent, etc structures of time-indexed sets

𝟙ᵗ : TSet
𝟙ᵗ = tset (λ _ → ⊤) (λ _ → id)

terminalᵗ : (A : TSet) → A →ᵗ 𝟙ᵗ
terminalᵗ A = tset-map (λ _ → tt)

𝟘ᵗ : TSet
𝟘ᵗ = tset (λ _ → ⊥) (λ _ → id)

initialᵗ : (A : TSet) → 𝟘ᵗ →ᵗ A
initialᵗ A = tset-map (λ ())

_×ᵗ_ : TSet → TSet → TSet
(tset A Af) ×ᵗ (tset B Bf) =
  tset
    (λ t → A t × B t)
    (λ p → mapˣ (Af p) (Bf p))

infix 23 _×ᵗ_

fstᵗ : ∀ {A B} → A ×ᵗ B →ᵗ A
fstᵗ = tset-map proj₁

sndᵗ : ∀ {A B} → A ×ᵗ B →ᵗ B
sndᵗ = tset-map proj₂

⟨_,_⟩ᵗ : ∀ {A B C} → A →ᵗ B → A →ᵗ C → A →ᵗ B ×ᵗ C
⟨ tset-map f , tset-map g ⟩ᵗ = tset-map < f , g >

_⇒ᵗ_ : TSet → TSet → TSet
(tset A Af) ⇒ᵗ (tset B Bf) =
  tset
    (λ t → (t' : Time) → t ≤ t' → A t' → B t')
    (λ p f t' q a → f t' (≤-trans p q) a)

infix 22 _⇒ᵗ_

appᵗ : ∀ {A B} → (A ⇒ᵗ B) ×ᵗ A →ᵗ B
appᵗ = tset-map λ { {t} (f , a) → f t ≤-refl a }

-- Semantics of the type modality `[ t ] A` as a graded comonad

[_]ᵒ : Time → TSet → TSet
[ τ ]ᵒ (tset A Af) =
  tset
    (λ t' → A (t' + τ))
    (λ p a → Af (+-mono-≤ p ≤-refl) a)

[_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → [ τ ]ᵒ A →ᵗ [ τ ]ᵒ B
[ τ ]ᶠ (tset-map f) = tset-map f

[_]-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵗ [ τ₂ ]ᵒ A
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

δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵗ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
δ {tset A Af} {τ₁} {τ₂} =
  tset-map
    (λ {t} a → Af (≤-reflexive (sym (+-assoc t τ₁ τ₂))) a)

δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵗ [ τ₁ + τ₂ ]ᵒ A
δ⁻¹ {tset A Af} {τ₁} {τ₂} =
  tset-map (λ {t} a → Af (≤-reflexive (+-assoc t τ₁ τ₂)) a)

-- Semantics of the context modality `Γ ⟨ t ⟩` as a graded monad

⟨_⟩ᵒ : Time → TSet → TSet
⟨ τ ⟩ᵒ (tset A Af) =
  tset
    (λ t' → τ ≤ t' × A (t' ∸ τ))
    (λ p (q , a) → ≤-trans q p , Af (∸-mono p (≤-refl {τ})) a)

⟨_⟩ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → ⟨ τ ⟩ᵒ A →ᵗ ⟨ τ ⟩ᵒ B
⟨ τ ⟩ᶠ (tset-map f) =
  tset-map
    (λ { (p , a) → p , f a })

⟨_⟩-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → ⟨ τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ A
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

μ : ∀ {A τ₁ τ₂} → ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A) →ᵗ ⟨ τ₁ + τ₂ ⟩ᵒ A
μ {tset A Af} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , q , a) → n≤k⇒m≤k∸n⇒n+m≤k τ₁ τ₂ t p q ,
                           Af (≤-reflexive (n∸m∸k≡n∸m+k t τ₁ τ₂)) a })

μ⁻¹ : ∀ {A τ₁ τ₂} → ⟨ τ₁ + τ₂ ⟩ᵒ A →ᵗ ⟨ τ₁ ⟩ᵒ (⟨ τ₂ ⟩ᵒ A)
μ⁻¹ {tset A Af} {τ₁} {τ₂} =
  tset-map
    (λ { {t} (p , a) → m+n≤o⇒m≤o τ₁ p ,
                       n+m≤k⇒m≤k∸n τ₁ τ₂ t p ,
                       Af (≤-reflexive (sym (n∸m∸k≡n∸m+k t τ₁ τ₂))) a })

-- Adjunction between the graded monad and comonad

η⊣ : ∀ {A τ} → A →ᵗ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
η⊣ {tset A Af} {τ} =
  tset-map
    (λ {t'} a → m≤n+m τ t' , Af (≤-reflexive (sym (m+n∸n≡m t' τ))) a)

ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵗ A
ε⊣ {tset A Af} {τ} =
  tset-map
    (λ { {t'} (p , a) → Af (n≤m⇒m∸n+n≤m τ t' p) a })
