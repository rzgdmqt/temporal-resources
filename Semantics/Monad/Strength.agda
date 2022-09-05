---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

module Semantics.Monad.Strength where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.TSets
open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Monad.Core

open import Util.Equality
open import Util.Operations
open import Util.Time

-- The strength of the monad generated by the operations in Op
--------------------------------------------------------------

-- Strength

mutual

  {-# TERMINATING #-}

  strˢ : ∀ {A B τ τ' t}
       → carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) t
       → Tˢ B τ t
       → Tˢ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ t
  strˢ {A} {B} {τ' = τ'} {t} v (leaf w) =
    leaf
      (pack-×ᵗ
        ((≤-trans (proj₁ v) (≤-reflexive (+-identityʳ _)) ,
           monotone A
             (≤-reflexive (cong (_∸ τ') (+-identityʳ _)))
             (proj₂ v)) ,
         w))
  strˢ {A} {B} {_} {τ'} {t} v (node op w k k-nat) =
    node op w
      (λ p y →
        strˢ {A} {B}
          ((monotone (⟨ τ' ⟩ᵒ A)
             (≤-trans
               (≤-reflexive (sym (+-assoc t _ _)))
               (+-monoˡ-≤ _ p))
             v))
          (k p y))
      (λ p q y →
        trans
          (cong₂ strˢ
            (cong₂ _,_
              (≤-irrelevant _ _)
              (trans
                (cong (λ p → monotone A p (proj₂ v))
                  (≤-irrelevant _ _))
                (sym
                  (monotone-trans A _
                    (∸-monoˡ-≤ τ' (+-monoˡ-≤ _ p))
                    (proj₂ v)))))
            (k-nat p q y))
          (strˢ-≤t-nat p _ (k q y)))
  strˢ {A} {B} {_} {τ'} {t} v (delay τ k) =
    delay τ
      (strˢ {A} {B}
        (monotone (⟨ τ' ⟩ᵒ A) (≤-reflexive (sym (+-assoc t _ _))) v)
        k)
     
  strˢ-≤t-nat : ∀ {A B τ τ'} → {t t' : ℕ} → (p : t ≤ t')
              → (v : carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) t)
              → (c : Tˢ B τ t)
              → strˢ {A = A} {B = B}
                  (monotone ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) p v)
                  (Tˢ-≤t p c)
              ≡ Tˢ-≤t p (strˢ {A = A} {B = B} v c)
  strˢ-≤t-nat {A} {B} p v (leaf w) =
    cong leaf
      (trans
        (cong pack-×ᵗ
          (cong (_, monotone B p w)
            (cong₂ _,_
              (≤-irrelevant _ _)
              (trans
                (trans
                  (monotone-trans A _ _ (proj₂ v))
                  (cong (λ p → monotone A p (proj₂ v)) (≤-irrelevant _ _)))
                (sym (monotone-trans A _ _ (proj₂ v)))))))
        (sym (pack-×ᵗ-monotone p _)))
  strˢ-≤t-nat {A} {B} p v (node op w k k-nat) =
    dcong₂ (node op (monotone ⟦ param op ⟧ᵍ p w))
      (ifun-ext (fun-ext (λ q → fun-ext (λ y →
        cong (λ v → strˢ {A} {B} v (k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y))
          (cong₂ _,_
            (≤-irrelevant _ _)
            (trans
              (monotone-trans A _ _ (proj₂ v))
              (cong (λ p → monotone A p (proj₂ v)) (≤-irrelevant _ _))))))))
      (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip))))))
  strˢ-≤t-nat {A} {B} {_} {τ'} {t} {t'} p v (delay τ k) =
    cong (delay τ)
      (trans
        (cong (λ v → strˢ {A} {B} v (Tˢ-≤t (+-monoˡ-≤ _ p) k))
          (cong₂ _,_
            (≤-irrelevant _ _)
            (trans
              (monotone-trans A _ _ (proj₂ v))
              (trans
                (cong (λ p → monotone A p (proj₂ v)) (≤-irrelevant _ _))
                (sym (monotone-trans A _ _ (proj₂ v)))))))
        (strˢ-≤t-nat
          (+-monoˡ-≤ τ p)
          (monotone (⟨ τ' ⟩ᵒ A) (≤-reflexive (sym (+-assoc t _ _))) v)
          k))

strᵀ : ∀ {A B τ τ'}
     → [ τ ]ᵒ (⟨ τ' ⟩ᵒ A) ×ᵗ Tᵒ B τ →ᵗ Tᵒ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ
strᵀ {A} {B} {τ} {τ'} =
  tset-map
    (λ vc → strˢ {A} {B} (proj₁ (unpack-×ᵗ vc)) (proj₂ (unpack-×ᵗ vc)))
    (λ p vc → trans
      (cong₂ strˢ
        (sym (cong proj₁ (unpack-×ᵗ-monotone {[ τ ]ᵒ (⟨ τ' ⟩ᵒ A)} {Tᵒ B τ} p vc)))
        (sym (cong proj₂ (unpack-×ᵗ-monotone {[ τ ]ᵒ (⟨ τ' ⟩ᵒ A)} {Tᵒ B τ} p vc))))
      (strˢ-≤t-nat p _ _))
