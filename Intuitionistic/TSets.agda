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

n≡m+k≤n' : ∀ {n n' m k} → n ≡ m + k → n ≤ n' → Σ[ m' ∈ ℕ ] (n' ≡ m' + k × m ≤ m')
n≡m+k≤n' {n' = n'} {m = m} p z≤n
  rewrite m+n≡0⇒m≡0 m (sym p) | m+n≡0⇒n≡0 m (sym p) =
    n' , sym (+-identityʳ n') , z≤n
n≡m+k≤n' {n' = .(suc _)} {m = zero} refl (s≤s {n''} {n'''} q) with n≡m+k≤n' {k = n''} refl q
... | p' , q' , r' = p' , trans (cong suc q') (sym (+-suc p' n'')) , r'
n≡m+k≤n' {n' = .(suc _)} {m = suc m} p (s≤s {n''} {n'''} q) with suc-injective p
... | s with n≡m+k≤n' {m = m} s q
... | p' , q' , r' = suc p' , cong suc q' , +-mono-≤ (≤-refl {1}) r'

-- Time-indexed sets (covariant presheaves indexed by `(ℕ,≤)`)

record TSet : Set₁ where
  constructor
    tset
  field
    carrier  : Time → Set
    monotone : ∀ {t t'} → t ≤ t' → carrier t → carrier t'

    -- TODO: also include the functor laws for refl-id and trans-∘

open TSet public

-- Maps of time-indexed sets

record _→ᵗ_ (A B : TSet) : Set where
  constructor
    tset-map
  field
    map-carrier : ∀ {t} → carrier A t → carrier B t

    -- TODO: also include naturality law

infix 20 _→ᵗ_

open _→ᵗ_ public

-- Identity and composition of maps of time-indexed sets

idᵗ : ∀ {A} → A →ᵗ A
idᵗ = tset-map id

_∘ᵗ_ : ∀ {A B C} → B →ᵗ C → A →ᵗ B → A →ᵗ C
(tset-map g) ∘ᵗ (tset-map f) = tset-map (g ∘ f)

infixr 9 _∘ᵗ_

-- Product, sum, exponent, etc structures of time-indexed sets

---- terminal object

𝟙ᵗ : TSet
𝟙ᵗ = tset (λ _ → ⊤) (λ _ → id)

terminalᵗ : ∀ {A} → A →ᵗ 𝟙ᵗ
terminalᵗ = tset-map (λ _ → tt)

---- initial object

𝟘ᵗ : TSet
𝟘ᵗ = tset (λ _ → ⊥) (λ _ → id)

initialᵗ : ∀ {A} → 𝟘ᵗ →ᵗ A
initialᵗ = tset-map (λ ())

---- products

_×ᵗ_ : TSet → TSet → TSet
(tset A Af) ×ᵗ (tset B Bf) =
  tset
    (λ t → A t × B t)
    (λ p → mapˣ (Af p) (Bf p))

infixr 23 _×ᵗ_

fstᵗ : ∀ {A B} → A ×ᵗ B →ᵗ A
fstᵗ = tset-map proj₁

sndᵗ : ∀ {A B} → A ×ᵗ B →ᵗ B
sndᵗ = tset-map proj₂

⟨_,_⟩ᵗ : ∀ {A B C} → A →ᵗ B → A →ᵗ C → A →ᵗ B ×ᵗ C
⟨ tset-map f , tset-map g ⟩ᵗ = tset-map < f , g >

mapˣᵗ : ∀ {A B C D} → A →ᵗ C → B →ᵗ D → A ×ᵗ B →ᵗ C ×ᵗ D
mapˣᵗ (tset-map f) (tset-map g) = tset-map (mapˣ f g)

---- exponentials

_⇒ᵗ_ : TSet → TSet → TSet
(tset A Af) ⇒ᵗ (tset B Bf) =
  tset
    (λ t → {t' : Time} → t ≤ t' → A t' → B t')
    (λ p f q a → f (≤-trans p q) a)

infix 22 _⇒ᵗ_

appᵗ : ∀ {A B} → (A ⇒ᵗ B) ×ᵗ A →ᵗ B
appᵗ = tset-map λ { {t} (f , a) → f ≤-refl a }

curryᵗ : ∀ {A B C} → A ×ᵗ B →ᵗ C → A →ᵗ B ⇒ᵗ C
curryᵗ {tset A Af} (tset-map f) = tset-map (λ a → λ p b → f (Af p a , b))

uncurryᵗ : ∀ {A B C} → A →ᵗ B ⇒ᵗ C → A ×ᵗ B →ᵗ C
uncurryᵗ (tset-map f) = tset-map λ { (a , b) → f a ≤-refl b }

