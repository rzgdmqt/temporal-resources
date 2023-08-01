module Util.Properties where 

open import Data.Nat.Base
open import Data.Empty
open import Util.Time

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

-------------------------------------------------------------
-- Set of usefull lemmas about equalities and inequalities --
-------------------------------------------------------------

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