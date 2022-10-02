---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

module Semantics.Model.Examples.TSets.Monad.Strength where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.Model.Examples.TSets.TSets
open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.Monad.Core

open import Util.Equality
open import Util.Operations
open import Util.Time

-- The strength of the monad generated by the operations in Op
--------------------------------------------------------------

mutual

  {-# TERMINATING #-}

  strˢ : ∀ {A B τ t}
       → carrier ([ τ ]ᵒ A) t
       → Tˢ B τ t
       → Tˢ (A ×ᵗ B) τ t
  strˢ {A} {B} v (leaf w) =
    leaf
      (monotone A (≤-reflexive (+-identityʳ _)) v , w)
  strˢ {A} {B} {_} {t} v (op-node {τ = τ} op w k k-nat) =
    op-node op w
      (λ p y →
        strˢ {A} {B}
          (monotone A
            (≤-trans
              (≤-reflexive (sym (+-assoc t (op-time op) τ)))
              (+-monoˡ-≤ τ p)) v)
          (k p y))
      (λ p q y →
        trans
          (cong₂ strˢ
            (trans
              (cong (λ p →  monotone A p v) (≤-irrelevant _ _))
              (sym
                (monotone-trans A _ _ _)))
            (k-nat p q y))
          (strˢ-≤t-nat p _ (k q y)))
  strˢ {A} {B} {_} {t} v (delay-node τ k) =
    delay-node τ
      (strˢ {A} {B}
        (monotone A (≤-reflexive (sym (+-assoc t τ _))) v)
        k)

  strˢ-≤t-nat : ∀ {A B τ} → {t t' : ℕ} → (p : t ≤ t')
              → (v : carrier ([ τ ]ᵒ A) t)
              → (c : Tˢ B τ t)
              → strˢ {A = A} {B = B}
                  (monotone ([ τ ]ᵒ A) p v)
                  (Tˢ-≤t p c)
              ≡ Tˢ-≤t p (strˢ {A = A} {B = B} v c)
  strˢ-≤t-nat {A} {B} {_} {t} {t'} p v (leaf w) =
    cong leaf
      (cong (_, monotone B p w)
        (trans
          (monotone-trans A _ _ v)
          (trans
            (cong (λ p → monotone A p v) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ v)))))
  strˢ-≤t-nat {A} {B} {_} {t} {t'} p v (op-node op w k k-nat) =
    dcong₂ (op-node op (monotone ⟦ param op ⟧ᵍ p w))
      (ifun-ext (fun-ext (λ q → fun-ext (λ y →
        cong (λ x → strˢ x (k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y))
          (trans
            (monotone-trans A _ _ v)
            (cong (λ p → monotone A p v) (≤-irrelevant _ _)))))))
      (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip))))))
  strˢ-≤t-nat {A} {B} {_} {t} {t'} p v (delay-node τ k) =
    cong (delay-node τ)
      (trans
        (cong (λ x → strˢ x (Tˢ-≤t (+-monoˡ-≤ τ p) k))
          (trans
            (monotone-trans A _ _ v)
            (trans
              (cong (λ p → monotone A p v) (≤-irrelevant _ _))
              (sym (monotone-trans A _ _ v)))))
        (strˢ-≤t-nat _ _ k))

τ-substˢ-strˢ : ∀ {A B τ τ' t}
              → (p : τ ≡ τ')
              → (x : carrier A (t + τ))
              → (c : Tˢ B τ t)
              → τ-substˢ p (strˢ x c)
              ≡ strˢ {A} (monotone A (+-monoʳ-≤ t (≤-reflexive p)) x) (τ-substˢ p c)
τ-substˢ-strˢ {A} refl x c =
  cong (λ x → strˢ x c) (sym
    (trans
      (cong (λ p → monotone A p x) (≤-irrelevant _ _))
      (monotone-refl A x)))

strᵀ : ∀ {A B τ}
     → [ τ ]ᵒ A ×ᵗ Tᵒ B τ →ᵗ Tᵒ (A ×ᵗ B) τ
strᵀ {A} {B} {τ} =
  tset-map
    (λ vc → strˢ {A} {B} (proj₁ vc) (proj₂ vc))
    (λ p vc → strˢ-≤t-nat p (proj₁ vc) (proj₂ vc))
