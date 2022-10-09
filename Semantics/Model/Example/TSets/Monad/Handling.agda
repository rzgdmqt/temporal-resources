--------------------------------------------------------------------
-- [-]-strong free graded monad generated by algebraic operations --
--------------------------------------------------------------------

module Semantics.Model.Example.TSets.Monad.Handling where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.Model.Example.TSets.TSets
open import Semantics.Model.Example.TSets.Modality.Future
open import Semantics.Model.Example.TSets.Modality.Past
open import Semantics.Model.Example.TSets.Monad.Core

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Effect handling for the graded monad generated by the operations in Op
-------------------------------------------------------------------------

-- T-algebra induced by an effect handler

mutual

  {-# TERMINATING #-}

  T-alg-of-handlerˢ : ∀ {A τ τ' t}
                    → carrier (Πᵗ Op (λ op → Πᵗ Time (λ τ'' →
                        ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                          ⇒ᵗ Tᵒ A (op-time op + τ'')))) t
                    → {t' : Time}
                    → t ≤ t'
                    → Tˢ (Tᵒ A τ') τ t'
                    → Tˢ A (τ + τ') t'

  T-alg-of-handlerˢ h p (leaf c) =
    c
  T-alg-of-handlerˢ {A} {_} {τ'} h p (op-node {τ = τ} op v k k-nat) =
    τ-substˢ
      (sym (+-assoc (op-time op) _ _))
      (map-carrier (h op (τ + τ'))
        (p ,
         v ,
         tset-map
           (λ { (q , y) → T-alg-of-handlerˢ h (≤-trans p (m+n≤o⇒m≤o _ q)) (k q y)})
           (λ { q (r , y) →
             trans
               (cong₂ (T-alg-of-handlerˢ h) (≤-irrelevant _ _) (k-nat q r y))
               (T-alg-of-handlerˢ-≤t-cod-nat _ h q (k r y)) })))
  T-alg-of-handlerˢ h p (delay-node τ k) =
    τ-substˢ
      (sym (+-assoc τ _ _))
      (delay-node τ
        (T-alg-of-handlerˢ h (≤-stepsʳ τ p) k))


  T-alg-of-handlerˢ-≤t-cod-nat : ∀ {A τ τ'} → {t t' : ℕ} → (p : t ≤ t')
                               → (h : carrier (Πᵗ Op (λ op → Πᵗ Time (λ τ'' →
                                        ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                                          ⇒ᵗ Tᵒ A (op-time op + τ'')))) t)
                               → {t'' : Time}
                               → (q : t' ≤ t'')
                               → (c : Tˢ (Tᵒ A τ') τ t')
                               → T-alg-of-handlerˢ h (≤-trans p q) (Tˢ-≤t q c)
                               ≡ Tˢ-≤t q (T-alg-of-handlerˢ h p c)
                           
  T-alg-of-handlerˢ-≤t-cod-nat p h q (leaf v) =
    refl
  T-alg-of-handlerˢ-≤t-cod-nat {A} {τ' = τ'} p h q (op-node {τ = τ} op v k k-nat) =
    trans
      (cong (τ-substˢ (sym (+-assoc (op-time op) _ _)))
        (trans
          (cong (map-carrier (h op (τ + τ')))
            (cong₂ _,_
              (≤-irrelevant _ _)
              (cong₂ _,_
                refl
                (dcong₂ tset-map
                  (ifun-ext (fun-ext (λ { (r , y) →
                    cong
                      (λ p → T-alg-of-handlerˢ h p (k (≤-trans (+-mono-≤ q (≤-reflexive refl)) r) y))
                      (≤-irrelevant _ _) })))
                  (ifun-ext (ifun-ext (fun-ext (λ _ → fun-ext (λ _ → uip)))))))))
          (map-nat (h op (τ + τ')) q (p , v , _))))
      (τ-substˢ-≤t (sym (+-assoc (op-time op) _ _)) _ _)
  T-alg-of-handlerˢ-≤t-cod-nat p h q (delay-node τ k) =
    trans
      (cong (τ-substˢ (sym (+-assoc τ _ _)))
        (cong (delay-node τ)
          (trans
            (cong (λ p → T-alg-of-handlerˢ h p (Tˢ-≤t (+-monoˡ-≤ τ q) k)) (≤-irrelevant _ _))
            (T-alg-of-handlerˢ-≤t-cod-nat (≤-stepsʳ τ p) h (+-monoˡ-≤ τ q) k))))
      (τ-substˢ-≤t (sym (+-assoc τ _ _)) q _)


  T-alg-of-handlerˢ-≤t-nat : ∀ {A τ τ'} → {t t' : ℕ} → (p : t ≤ t')
                           → (h : carrier (Πᵗ Op (λ op → Πᵗ Time (λ τ'' →
                                    ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                                      ⇒ᵗ Tᵒ A (op-time op + τ'')))) t)
                           → {t'' : Time}
                           → (q : t' ≤ t'')
                           → (c : Tˢ (Tᵒ A τ') τ t'')
                           → T-alg-of-handlerˢ
                               (monotone (Πᵗ Op (λ op → Πᵗ Time (λ τ'' →
                                           ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ
                                             ⇒ᵗ (Tᵒ A τ''))) ⇒ᵗ Tᵒ A (op-time op + τ'')))) p h)
                               q c
                           ≡ T-alg-of-handlerˢ h (≤-trans p q) c
  T-alg-of-handlerˢ-≤t-nat p h q (leaf v) =
    refl
  T-alg-of-handlerˢ-≤t-nat {A} {τ' = τ'} p h q (op-node {τ = τ} op v k k-nat) =
    cong
      (τ-substˢ (sym (+-assoc (op-time op) τ τ')))
      (cong (map-carrier (h op (τ + τ')))
        (cong₂ _,_
          refl
          (cong₂ _,_
            refl
            (dcong₂ tset-map
              (ifun-ext (fun-ext (λ { (r , y) →
                trans
                  (T-alg-of-handlerˢ-≤t-nat p h _ (k r y))
                  (cong (λ p → T-alg-of-handlerˢ h p (k r y)) (≤-irrelevant _ _)) })))
              (ifun-ext (ifun-ext (fun-ext (λ _ → fun-ext (λ _ → uip)))))))))
  T-alg-of-handlerˢ-≤t-nat p h q (delay-node τ k) =
    cong (τ-substˢ (sym (+-assoc τ _ _)))
      (cong (delay-node τ)
        (trans
          (T-alg-of-handlerˢ-≤t-nat p h _ k)
          (cong (λ p → T-alg-of-handlerˢ h p k) (≤-irrelevant _ _))))


T-alg-of-handlerᵀ : ∀ {A τ τ'}
                  → Πᵗ Op (λ op → Πᵗ Time (λ τ'' →
                     ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                       ⇒ᵗ Tᵒ A (op-time op + τ'')))
                  →ᵗ Tᵒ (Tᵒ A τ') τ ⇒ᵗ Tᵒ A (τ + τ')
T-alg-of-handlerᵀ {A} {τ} {τ'} =
  tset-map
    (λ {t} h →
      tset-map
        (λ { {t'} (p , c) →
          T-alg-of-handlerˢ h p c })
        (λ { {t'} {t''} p (q , c) → 
          T-alg-of-handlerˢ-≤t-cod-nat q h p c }))            
    (λ {t} {t'} p h →
      dcong₂ tset-map
        (ifun-ext (fun-ext (λ pc → T-alg-of-handlerˢ-≤t-nat p h (proj₁ pc) (proj₂ pc))))
        (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ rc → uip))))))
