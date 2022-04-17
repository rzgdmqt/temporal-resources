---------------------------------------------------------
-- Time for temporal effect annotations and presheaves --
---------------------------------------------------------

module Util.Time where

open import Data.Nat public
open import Data.Nat.Properties public

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding (Extensionality)
open Eq.≡-Reasoning

-- Time steps and annotations

Time : Set
Time = ℕ

-- Some auxiliary lemmas concerning ∸

n≤k⇒m≤k∸n⇒n+m≤k : (n m k : Time) → n ≤ k → m ≤ k ∸ n → n + m ≤ k
n≤k⇒m≤k∸n⇒n+m≤k zero m k z≤n q = q
n≤k⇒m≤k∸n⇒n+m≤k (suc n) m (suc k) (s≤s p) q =
  +-monoʳ-≤ 1 (n≤k⇒m≤k∸n⇒n+m≤k n m k p q)

n≤n∸m+m : (n m : Time) → n ≤ n ∸ m + m
n≤n∸m+m n       zero    = ≤-stepsʳ 0 ≤-refl
n≤n∸m+m zero    (suc m) = z≤n
n≤n∸m+m (suc n) (suc m) =
  ≤-trans
    (+-monoʳ-≤ 1 (n≤n∸m+m n m))
    (≤-reflexive (sym (+-suc (n ∸ m) (m))))

n≤m⇒m∸n+n≤m : (n m : Time) → n ≤ m → m ∸ n + n ≤ m
n≤m⇒m∸n+n≤m zero m z≤n =
  ≤-reflexive (+-identityʳ m)
n≤m⇒m∸n+n≤m (suc n) (suc m) (s≤s p) =
  ≤-trans
    (≤-reflexive (+-suc (m ∸ n) n))
    (+-monoʳ-≤ 1 (n≤m⇒m∸n+n≤m n m p))

n+m≤k⇒m≤k∸n : (n m k : Time) → n + m ≤ k → m ≤ k ∸ n
n+m≤k⇒m≤k∸n zero    m       k       p       = p
n+m≤k⇒m≤k∸n (suc n) zero    k       p       = z≤n
n+m≤k⇒m≤k∸n (suc n) (suc m) (suc k) (s≤s p) = n+m≤k⇒m≤k∸n n (suc m) k p

n∸m∸k≡n∸m+k : (n m k : Time) → n ∸ m ∸ k ≡ n ∸ (m + k)
n∸m∸k≡n∸m+k zero    zero    k       = refl
n∸m∸k≡n∸m+k zero    (suc m) zero    = refl
n∸m∸k≡n∸m+k zero    (suc m) (suc k) = refl
n∸m∸k≡n∸m+k (suc n) zero    k       = refl
n∸m∸k≡n∸m+k (suc n) (suc m) k       = n∸m∸k≡n∸m+k n m k

n+m∸n+k≡m∸k : (n : Time) → {m k : Time} → k ≤ m → n + m ∸ (n + k) ≡ m ∸ k
n+m∸n+k≡m∸k zero {zero} {k} p = refl
n+m∸n+k≡m∸k zero {suc m} {zero} p = refl
n+m∸n+k≡m∸k zero {suc m} {suc k} p = refl
n+m∸n+k≡m∸k (suc n) {zero} {zero} p = n∸n≡0 (n + zero)
n+m∸n+k≡m∸k (suc n) {suc m} {zero} p =
  trans
    (trans
      (cong (n + suc m ∸_) (+-identityʳ n))
      (trans
        (trans
          (m+n∸m≡n n (suc m))
          (sym (cong suc (m+n∸m≡n n m))))
        (cong (λ l → suc (n + m ∸ l)) (sym (+-identityʳ n)))))
    (cong suc (n+m∸n+k≡m∸k n z≤n))
n+m∸n+k≡m∸k (suc n) {suc m} {suc k} (s≤s p) =
  trans
    (cong₂ _∸_ (+-suc n m) (+-suc n k))
    (n+m∸n+k≡m∸k n p)

n≡m+k≤n' : ∀ {n n' m k} → n ≡ m + k → n ≤ n' → Σ[ m' ∈ ℕ ] (n' ≡ m' + k × m ≤ m')
n≡m+k≤n' {n' = n'} {m = m} p z≤n
  rewrite m+n≡0⇒m≡0 m (sym p) | m+n≡0⇒n≡0 m (sym p) =
    n' , sym (+-identityʳ n') , z≤n
n≡m+k≤n' {n' = .(suc _)} {m = zero} refl (s≤s {n''} {n'''} q) with n≡m+k≤n' {k = n''} refl q
... | p' , q' , r' = p' , trans (cong suc q') (sym (+-suc p' n'')) , r'
n≡m+k≤n' {n' = .(suc _)} {m = suc m} p (s≤s {n''} {n'''} q) with suc-injective p
... | s with n≡m+k≤n' {m = m} s q
... | p' , q' , r' = suc p' , cong suc q' , +-mono-≤ (≤-refl {1}) r'
