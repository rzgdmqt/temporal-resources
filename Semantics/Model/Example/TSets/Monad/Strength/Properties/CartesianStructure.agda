{-# OPTIONS --experimental-lossy-unification #-}

--------------------------------------------------------------------
-- [-]-strong free graded monad generated by algebraic operations --
--------------------------------------------------------------------

module Semantics.Model.Example.TSets.Monad.Strength.Properties.CartesianStructure where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.Model.Example.TSets.TSets
open import Semantics.Model.Example.TSets.Modality.Future
open import Semantics.Model.Example.TSets.Modality.Past
open import Semantics.Model.Example.TSets.Modality.Adjunction
open import Semantics.Model.Example.TSets.Monad.Core
open import Semantics.Model.Example.TSets.Monad.Strength
open import Semantics.Model.Example.TSets.Monad.Effects

open import Semantics.Model.Category.Derived TSetCat
open import Semantics.Model.Modality.Adjunction.Derived TSetCat TSetFut TSetPas TSetAdj

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Strength's interaction with the Cartesian-monoidal structure

strˢ-sndᵗ : ∀ {A B τ t}
          → (v : carrier A (t + τ))
          → (c : Tˢ B τ t)
          → Tˢᶠ sndᵗ (strˢ {A} v c)
          ≡ c
          
strˢ-sndᵗ v (leaf w) =
  refl
strˢ-sndᵗ {A} {_} {_} {t} v (op-node {τ = τ} op w k k-nat) =
  dcong₂ (op-node op w)
    (ifun-ext (fun-ext (λ p → fun-ext (λ y →
      strˢ-sndᵗ
        (monotone A (≤-trans (≤-reflexive (sym (+-assoc t (op-time op) τ))) (+-monoˡ-≤ τ p)) v)
        (k p y)))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext λ q → fun-ext λ y → uip))))
strˢ-sndᵗ {A} {_} {τ''} {t} v (delay-node {τ' = τ'} τ k) =
  cong (delay-node τ) (strˢ-sndᵗ (monotone A (≤-reflexive (sym (+-assoc t τ τ'))) v) k)

strᵀ-sndᵗ : ∀ {A B τ}
          → Tᶠ sndᵗ ∘ᵗ strᵀ {A} {B} {τ}
         ≡ᵗ sndᵗ

strᵀ-sndᵗ {A} {B} {τ} =
  eqᵗ (λ { {t} (x , c) → strˢ-sndᵗ x c })

-- Strength's interaction with the Cartesian-monoidal structure

strˢ-assoc : ∀ {A B C τ t}
           → (x : carrier A (t + τ))
           → (y : carrier B (t + τ))
           → (c : Tˢ C τ t)
           → map-carrier
               (Tᶠ ×ᵐ-assoc ∘ᵗ strᵀ {A ×ᵗ B} ∘ᵗ mapˣᵗ ([]-monoidal {A} {B}) idᵗ ∘ᵗ ×ᵐ-assoc⁻¹)
               {t}
               (x , y , c)
           ≡ map-carrier (strᵀ ∘ᵗ mapˣᵗ idᵗ strᵀ) {t} (x , y , c)

strˢ-assoc {A} {B} {C} x y (leaf v) =
  cong leaf
    (cong₂ _,_
      (trans
        (monotone-trans A _ _ _)
        (trans
          (monotone-trans A _ _ _)
          (cong (λ p → monotone A p x) (≤-irrelevant _ _))))
      (cong₂ _,_
        (trans
          (monotone-trans B _ _ _)
          (trans
            (monotone-trans B _ _ _)
            (cong (λ p → monotone B p y) (≤-irrelevant _ _))))
        refl))
        
strˢ-assoc {A} {B} {C} {_} {t} x y (op-node {τ = τ} op v k k-nat) =
  dcong₂
    {A = {t' : Time} → t + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ (A ×ᵗ (B ×ᵗ C)) τ t'}
    {B = λ k' → {t' t'' : Time} (p : t' ≤ t'') (q : t + op-time op ≤ t') (y₁ : carrier ⟦ arity op ⟧ᵍ t')
              → k' (≤-trans q p) (monotone ⟦ arity op ⟧ᵍ p y₁) ≡ Tˢ-≤t p (k' q y₁)}
    {C = Tˢ (A ×ᵗ (B ×ᵗ C)) (op-time op + τ) t}
    (op-node op v)
    (ifun-ext (fun-ext (λ p → fun-ext (λ z →
      trans
        (cong (Tˢᶠ (tset-map (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) (λ p₁ x₂ → refl)))
          (cong (λ xy → strˢ {A ×ᵗ B} xy (k p z))
            (cong₂ _,_
              (trans
                (monotone-trans A _ _ _)
                (trans
                  (monotone-trans A _ _ _)
                  (sym
                    (trans
                      (monotone-trans A _ _ _)
                      (trans
                        (monotone-trans A _ _ _)
                        (cong (λ p → monotone A p x) (≤-irrelevant _ _)))))))
              (trans
                (monotone-trans B _ _ _)
                (trans
                  (monotone-trans B _ _ _)
                  (sym
                    (trans
                      (monotone-trans B _ _ _)
                      (trans
                        (monotone-trans B _ _ _)
                        (cong (λ p → monotone B p y) (≤-irrelevant _ _))))))))))
        (strˢ-assoc
          (monotone A (≤-trans (≤-reflexive (sym (+-assoc t (op-time op) τ))) (+-monoˡ-≤ τ p)) x)
          (monotone B (≤-trans (≤-reflexive (sym (+-assoc t (op-time op) τ))) (+-monoˡ-≤ τ p)) y)
          (k p z))))))
    (ifun-ext (λ {t' : Time} → ifun-ext (λ {t'' : Time} →
      fun-ext (λ (p : t' ≤ t'') → fun-ext (λ (q : t + op-time op ≤ t') → fun-ext (λ (z : carrier ⟦ arity op ⟧ᵍ t') →
        uip))))))    -- NOTE: filling in this UIP usage makes typechecking this file extremely slow
        
strˢ-assoc {A} {B} {C} {_} {t} x y (delay-node {τ' = τ'} τ k) =
  cong (delay-node τ)
    (trans
      (cong (Tˢᶠ (tset-map (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁) (λ p x₁ → refl)))
        (cong (λ x → strˢ x k)
          (cong₂ _,_
            (trans
              (monotone-trans A _ _ _)
              (trans
                (monotone-trans A _ _ _)
                (sym
                  (trans
                    (monotone-trans A _ _ _)
                    (trans
                      (monotone-trans A _ _ _)
                      (cong (λ p → monotone A p x) (≤-irrelevant _ _)))))))
            (trans
              (monotone-trans B _ _ _)
              (trans
                (monotone-trans B _ _ _)
                (sym
                  (trans
                    (monotone-trans B _ _ _)
                    (trans
                      (monotone-trans B _ _ _)
                      (cong (λ p → monotone B p y) (≤-irrelevant _ _))))))))))
      (strˢ-assoc
        (monotone A (≤-reflexive (sym (+-assoc t τ τ'))) x)
        (monotone B (≤-reflexive (sym (+-assoc t τ τ'))) y) k) )

strᵀ-assoc : ∀ {A B C τ}
           →    Tᶠ ×ᵐ-assoc
             ∘ᵗ strᵀ {A ×ᵗ B} {C}
             ∘ᵗ mapˣᵗ ([]-monoidal {A} {B}) idᵗ ∘ᵗ ×ᵐ-assoc⁻¹
          ≡ᵗ    strᵀ {A}
             ∘ᵗ mapˣᵗ idᵗ (strᵀ {B} {C} {τ})

strᵀ-assoc {A} {B} {C} {τ} =
  eqᵗ (λ { {t} (x , y , c) → strˢ-assoc x y c })

