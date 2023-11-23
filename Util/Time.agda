---------------------------------------------------------
-- Time for temporal effect annotations and presheaves --
---------------------------------------------------------

module Util.Time where

open import Data.Nat public
open import Data.Nat.Properties public

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Util.Equality

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


n≡m+k≤n' : ∀ {n n' m k} → n ≡ m + k → n ≤ n' → Σ[ m' ∈ Time ] (n' ≡ m' + k × m ≤ m')
n≡m+k≤n' {n' = n'} {m = m} p z≤n
  rewrite m+n≡0⇒m≡0 m (sym p) | m+n≡0⇒n≡0 m (sym p) =
    n' , sym (+-identityʳ n') , z≤n
n≡m+k≤n' {n' = .(suc _)} {m = zero} refl (s≤s {n''} {n'''} q) with n≡m+k≤n' {k = n''} refl q
... | p' , q' , r' = p' , trans (cong suc q') (sym (+-suc p' n'')) , r'
n≡m+k≤n' {n' = .(suc _)} {m = suc m} p (s≤s {n''} {n'''} q) with suc-injective p
... | s with n≡m+k≤n' {m = m} s q
... | p' , q' , r' = suc p' , cong suc q' , +-mono-≤ (≤-refl {1}) r'


n≤k⇒¬n≤m+k-contradiction : ∀ {n m k} → n ≤ k → ¬ (n ≤ m + k) → ⊥
n≤k⇒¬n≤m+k-contradiction {n} {zero} {k} p q = q p
n≤k⇒¬n≤m+k-contradiction {.zero} {suc m} {k} z≤n q = q z≤n
n≤k⇒¬n≤m+k-contradiction {.(suc _)} {suc m} {.(suc _)} (s≤s p) q =
  n≤k⇒¬n≤m+k-contradiction {_} {m} {_} p
    (λ r → q (+-monoʳ-≤ 1 (≤-trans (≤-step r) (≤-reflexive (sym (+-suc m _))))))


sucn≤m⇒m+k≤n-contradiction : ∀ {n m k} → suc n ≤ m → m + k ≤ n → ⊥
sucn≤m⇒m+k≤n-contradiction {suc n} {suc m} {zero} (s≤s p) (s≤s q) =
  ≤⇒≯ p (+-monoʳ-≤ 1 (≤-trans (≤-reflexive (sym (+-identityʳ m))) q))
sucn≤m⇒m+k≤n-contradiction {suc n} {suc m} {suc k} (s≤s p) (s≤s q) =
  ≤⇒≯ p (+-monoʳ-≤ 1 (m+n≤o⇒m≤o m q))


n∸m≤zero⇒n∸m≡0 : ∀ {n m} → n ∸ m ≤ zero → n ∸ m ≡ 0
n∸m≤zero⇒n∸m≡0 {.zero} {zero} z≤n = refl
n∸m≤zero⇒n∸m≡0 {zero} {suc m} p = refl
n∸m≤zero⇒n∸m≡0 {suc n} {suc m} p = n∸m≤zero⇒n∸m≡0 {n} {m} p


¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m : ∀ {n m k}
                       → ¬ (k ≤ m)
                       → k ∸ m ≤ n
                       → n + m ∸ k ≡ n ∸ (k ∸ m)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {zero} {zero} {zero} p q =
  refl
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {zero} {suc m} {zero} p q =
  ⊥-elim (p z≤n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {zero} {suc m} {suc k} p q =
  ⊥-elim (p (+-monoʳ-≤ 1 (m∸n≡0⇒m≤n (n∸m≤zero⇒n∸m≡0 {k} {m} q))))
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {zero} {zero} p q =
  ⊥-elim (p z≤n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {zero} {suc k} p q =
  cong (_∸ k) (+-identityʳ  n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {suc m} {zero} p q =
  ⊥-elim (p z≤n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {suc m} {suc k} p q =
  trans
    (cong (_∸ k) (+-suc n m))
    (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {m} {k} (λ r → p (+-monoʳ-≤ 1 r)) q)


m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] : ∀ {n m k}
                         → m ≤ k
                         → ¬ (n + m ≤ k)
                         → n + m ∸ k ≡ n ∸ (k ∸ m)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {zero} {zero} {zero} p q =
  refl
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {zero} {zero} {suc k} p q =
  refl
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {zero} {suc m} {suc k} p q = 
  ⊥-elim (q p)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {zero} {zero} p q =
  cong suc (+-identityʳ _)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {zero} {suc k} p q = 
  cong (_∸ k) (+-identityʳ _)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {suc m} {suc k} (s≤s p) q =
  trans
    (cong (_∸ k) (trans (+-comm n (suc m)) (cong suc (+-comm m n))))
    (m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {m} {k} p
      (λ r → q (≤-trans (≤-reflexive (cong suc (+-comm n (suc m))))
        (≤-trans (≤-reflexive (cong suc (cong suc (+-comm m n)))) (+-monoʳ-≤ 1 r)))))


≤-extend : ∀ τ' τ'' τ → τ'' ≤ τ → τ' + τ'' ≤ τ' + τ
≤-extend zero τ'' τ p = p
≤-extend (suc τ') τ'' τ p = s≤s (≤-extend τ' τ'' τ p)

a+[b∸a]≡b : ∀ {a b} → {p : a ≤ b} → a + (b ∸ a) ≡ b 
a+[b∸a]≡b {a} {b} {p} = 
    begin 
        a + (b ∸ a) ≡⟨ sym (+-∸-assoc a p) ⟩ 
        (a + b) ∸ a ≡⟨ +-∸-comm {m = a} b {o = a} ≤-refl ⟩ 
        (a ∸ a) + b ≡⟨ cong (_+ b) (n∸n≡0 a) ⟩  
        0 + b 
    ∎

τ≡τ∸τ'+τ' : ∀ τ τ' → τ ∸ (τ' ∸ τ') ≡ τ
τ≡τ∸τ'+τ' τ τ' = 
    begin 
        τ ∸ (τ' ∸ τ') ≡⟨ cong (τ ∸_) (n∸n≡0 τ') ⟩  
        τ ∸ 0 ≡⟨ refl ⟩ 
        τ
    ∎

τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ : ∀ τ τ₁ τ₂ τ₃ → τ + (τ₁ + τ₂ + τ₃) ≡ τ + (τ₁ + (τ₂ + τ₃))
τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ τ τ₁ τ₂ τ₃ = 
    begin 
        τ + (τ₁ + τ₂ + τ₃) ≡⟨ cong (τ +_) (+-assoc τ₁ τ₂ τ₃) ⟩  
        τ + (τ₁ + (τ₂ + τ₃))
    ∎

τ-≤-substᵣ : ∀ {τ τ' τ''} → τ' ≡ τ'' → τ ≤ τ'' → τ ≤ τ'
τ-≤-substᵣ refl q = q

τ-≤-substₗ : ∀ {τ τ' τ''} → τ' ≡ τ'' → τ' ≤ τ → τ'' ≤ τ
τ-≤-substₗ refl p = p


step-time-eq : ∀ τ τ₁ τ' τ'' τ''' → (q : τ + τ₁ ≡ τ'' + τ''') → τ + (τ₁ + τ') ≡ τ'' + (τ''' + τ')
step-time-eq τ τ₁ τ' τ'' τ''' q = 
    begin 
        τ + (τ₁ + τ') ≡⟨ sym (+-assoc τ τ₁ τ') ⟩
        (τ + τ₁) + τ' ≡⟨ cong (_+ τ') q ⟩
        (τ'' + τ''') + τ' ≡⟨ +-assoc τ'' τ''' τ' ⟩
        τ'' + (τ''' + τ')
    ∎


lemma : ∀ τ τ' τ₁ → τ ≤ τ₁ → τ + τ + (τ₁ ∸ τ + τ') ≡ τ + (τ₁ + τ')
lemma τ τ' τ₁ p =
    begin 
        τ + τ + (τ₁ ∸ τ + τ') ≡⟨ +-assoc τ τ (τ₁ ∸ τ + τ') ⟩  
        τ + (τ + (τ₁ ∸ τ + τ')) ≡⟨ cong (τ +_ ) (cong (τ +_) ( sym (+-∸-comm τ' p))) ⟩ 
        τ + (τ + (τ₁ + τ' ∸ τ)) ≡⟨ cong (τ +_ ) (cong (τ +_) (cong (_∸ τ) (+-comm τ₁ τ')) ) ⟩ 
        τ + (τ + (τ' + τ₁ ∸ τ)) ≡⟨ cong (τ +_ ) (cong (τ +_) (+-∸-assoc τ' p)) ⟩ 
        τ + (τ + (τ' + (τ₁ ∸ τ))) ≡⟨ cong (τ +_ ) (sym (+-assoc τ τ' (τ₁ ∸ τ))) ⟩ 
        τ + (τ + τ' + (τ₁ ∸ τ)) ≡⟨ cong (τ +_) (cong (_+ (τ₁ ∸ τ)) (+-comm τ τ')) ⟩
        τ + (τ' + τ + (τ₁ ∸ τ)) ≡⟨ cong (τ +_)  (+-assoc τ' τ (τ₁ ∸ τ))  ⟩
        τ + (τ' + (τ + (τ₁ ∸ τ))) ≡⟨ cong (τ +_) (cong (τ' +_) (a+[b∸a]≡b {a = τ } {b = τ₁} {p = p})) ⟩
        τ + (τ' + τ₁) ≡⟨ cong (τ +_) (+-comm τ' τ₁) ⟩
        τ + (τ₁ + τ')
    ∎

τ∸τ'≤τ : ∀ τ τ' → τ ∸ τ' ≤ τ
τ∸τ'≤τ zero zero = ≤-refl
τ∸τ'≤τ zero (suc τ') = ≤-refl
τ∸τ'≤τ (suc τ) zero = ≤-refl
τ∸τ'≤τ (suc τ) (suc τ') = ≤-trans (τ∸τ'≤τ τ τ') (n≤1+n τ)

m≡n⇒m≤n : ∀ {m n} → m ≡ n → m ≤ n
m≡n⇒m≤n {zero} {n} p = z≤n
m≡n⇒m≤n {suc m} {suc n} p = s≤s (m≡n⇒m≤n (suc-injective p))

τ''∸τ'+τ≤τ''∸τ'+τ' : ∀ τ'' τ' τ → τ ≤ τ' → τ'' ∸ τ' + τ ≤ τ'' ∸ τ' + τ'
τ''∸τ'+τ≤τ''∸τ'+τ' τ'' zero zero p = ≤-refl
τ''∸τ'+τ≤τ''∸τ'+τ' τ'' (suc τ') τ p = ≤-extend (τ'' ∸ suc τ') τ (suc τ') p

τ''∸τ'+τ≤τ'' : ∀ τ'' τ' τ → τ ≤ τ' → τ' ≤ τ'' → τ'' ∸ τ' + τ ≤ τ''
τ''∸τ'+τ≤τ'' τ'' τ' τ p q = 
    ≤-trans 
      (τ''∸τ'+τ≤τ''∸τ'+τ' τ'' τ' τ p) 
      (τ-≤-substₗ (+-∸-comm τ' q) (τ-≤-substₗ (sym (m+n∸n≡m τ'' τ')) ≤-refl))

sucn≤n⇒⊥ : ∀ τ → suc τ ≤ τ → ⊥
sucn≤n⇒⊥ (suc τ) (s≤s p) = sucn≤n⇒⊥ τ p

sucn≡n+1 : ∀ {n} → n + 1 ≡ suc n
sucn≡n+1 {zero} = refl
sucn≡n+1 {suc n} = cong suc (sucn≡n+1 {n})

n+sucm≤n⇒⊥ : ∀ {m n} → n + suc m ≤ n → ⊥
n+sucm≤n⇒⊥ {zero} {suc n} (s≤s p) = sucn≤n⇒⊥ n (τ-≤-substₗ sucn≡n+1 p)
n+sucm≤n⇒⊥ {suc m} {suc n} (s≤s p) = n+sucm≤n⇒⊥ p

a+b∸a≡b : ∀ {a b} → a + b ∸ a ≡ b 
a+b∸a≡b {a} {b} = 
    begin 
        (a + b) ∸ a ≡⟨ +-∸-comm {m = a} b {o = a} ≤-refl ⟩ 
        (a ∸ a) + b ≡⟨ cong (_+ b) (n∸n≡0 a) ⟩  
        0 + b 
    ∎

m≤n+k⇒m∸k≤n : ∀ m n k → m ≤ n + k → m ∸ k ≤ n
m≤n+k⇒m∸k≤n m n zero p = τ-≤-substᵣ (sym (+-identityʳ n)) p
m≤n+k⇒m∸k≤n zero n (suc k) p = z≤n
m≤n+k⇒m∸k≤n (suc m) zero (suc k) (s≤s p) = τ-≤-substₗ (sym (m≤n⇒m∸n≡0 p)) ≤-refl
m≤n+k⇒m∸k≤n (suc m) (suc n) (suc k) (s≤s p) = 
    m≤n+k⇒m∸k≤n m (suc n) k (τ-≤-substᵣ (sym (+-suc n k)) p)

0+[τ''+τ'+τ]≡τ'+[τ+τ''] : ∀ τ τ' τ'' → 0 + (τ'' + τ' + τ) ≡ τ' + (τ + τ'')
0+[τ''+τ'+τ]≡τ'+[τ+τ''] τ τ' τ'' = 
    begin 
        0 + (τ'' + τ' + τ) ≡⟨ refl ⟩ 
        τ'' + τ' + τ ≡⟨ +-assoc τ'' τ' τ ⟩  
        τ'' + (τ' + τ) ≡⟨ +-comm τ'' (τ' + τ) ⟩  
        τ' + τ + τ'' ≡⟨ +-assoc τ' τ τ'' ⟩  
        τ' + (τ + τ'')
    ∎

τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ : ∀ τ τ₁ τ₂ τ₄ → τ + τ₂ ≡ τ₁ + τ₄ → τ₂ + τ ≡ τ₄ + τ₁
τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ τ₁ τ₂ τ₄ p = 
    begin 
        τ₂ + τ ≡⟨ +-comm τ₂ τ ⟩ 
        τ + τ₂ ≡⟨ p ⟩
        τ₁ + τ₄ ≡⟨ +-comm τ₁ τ₄ ⟩
        τ₄ + τ₁ 
    ∎

a≤b⇒b≤a⇒a≡b : {a b : Time} → a ≤ b → b ≤ a → a ≡ b
a≤b⇒b≤a⇒a≡b z≤n z≤n = refl
a≤b⇒b≤a⇒a≡b (s≤s a≤b) (s≤s b≤a) = cong suc (a≤b⇒b≤a⇒a≡b a≤b b≤a) 

τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] : ∀ τ τ₁ τ₂ τ₃ τ₄
            → τ + τ₂ ≡ τ₁ + τ₄ 
            → τ + (τ₂ + τ₃) ≡ τ₁ + (τ₄ + τ₃)
τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] τ τ₁ τ₂ τ₃ τ₄ p = 
    begin 
        τ + (τ₂ + τ₃) ≡⟨ sym (+-assoc τ τ₂ τ₃) ⟩
        τ + τ₂ + τ₃ ≡⟨ cong (_+ τ₃) p ⟩
        τ₁ + τ₄ + τ₃ ≡⟨ +-assoc τ₁ τ₄ τ₃ ⟩
        τ₁ + (τ₄ + τ₃) 
    ∎

τ'''+[τ+τ']≡τ'+τ'''+τ : ∀ τ τ' τ''' → τ''' + (τ + τ') ≡ τ' + τ''' + τ
τ'''+[τ+τ']≡τ'+τ'''+τ τ τ' τ''' = 
    begin 
        τ''' + (τ + τ') ≡⟨ sym (+-assoc τ''' τ τ') ⟩
        τ''' + τ + τ' ≡⟨ +-comm (τ''' + τ) τ' ⟩
        τ' + (τ''' + τ) ≡⟨ sym (+-assoc τ' τ''' τ) ⟩
        τ' + τ''' + τ
    ∎ 

τ+sucτ''≡τ'+sucτ'''⇒τ+τ''≡τ'+τ''' : ∀ τ τ' τ'' τ''' → τ + suc τ'' ≡ τ' + suc τ''' → τ + τ'' ≡ τ' + τ'''
τ+sucτ''≡τ'+sucτ'''⇒τ+τ''≡τ'+τ''' τ τ' τ'' τ''' p = suc-injective (
    begin 
        suc (τ + τ'') ≡⟨ sym (+-suc τ τ'') ⟩
        τ + suc τ'' ≡⟨ p ⟩
        τ' + suc τ''' ≡⟨ +-suc τ' τ''' ⟩
        suc (τ' + τ''')
    ∎ )

subst-left : ∀ a b c d → a + b ≡ c + d → a ≡ c → a + b ≡ a + d
subst-left a b .a d p refl = p

τ≤τ'∧τ+τ''≡τ'+τ'''⇒τ''≤τ''' : ∀ τ τ' τ'' τ''' → τ ≤ τ' → τ + τ'' ≡ τ' + τ''' → τ''' ≤ τ''
τ≤τ'∧τ+τ''≡τ'+τ'''⇒τ''≤τ''' τ τ' τ'' zero p q = z≤n
τ≤τ'∧τ+τ''≡τ'+τ'''⇒τ''≤τ''' τ τ' zero (suc τ''') p q = 
    m≡n⇒m≤n 
        (sym (+-cancelˡ-≡ τ 
            (subst-left τ zero τ' (suc τ''') 
                q 
                (a≤b⇒b≤a⇒a≡b p 
                    (≤-trans 
                        (≤-stepsʳ (suc τ''') ≤-refl) 
                        (m≡n⇒m≤n (trans (sym q) (+-identityʳ τ)))))))) 
τ≤τ'∧τ+τ''≡τ'+τ'''⇒τ''≤τ''' τ τ' (suc τ'') (suc τ''') p q = 
    s≤s (τ≤τ'∧τ+τ''≡τ'+τ'''⇒τ''≤τ''' τ τ' τ'' τ''' p (τ+sucτ''≡τ'+sucτ'''⇒τ+τ''≡τ'+τ''' τ τ' τ'' τ''' q))  

sucτ∸τ≡1 : (τ : Time) → suc τ ∸ τ ≡ 1
sucτ∸τ≡1 zero = refl
sucτ∸τ≡1 (suc τ) = sucτ∸τ≡1 τ

second-part-equality : ∀ (a b c d e : Time) → a ≡ b + c → b + d ≡ a + e → c + e ≡ d
second-part-equality a b c d e p q = 
  +-cancelˡ-≡ b 
    (sym (trans q 
      (sym (trans 
        (sym (+-assoc b c e)) 
        (cong (_+ e) (sym p)))))) 