--------------------------------------------------------------------
-- [-]-strong free graded monad generated by algebraic operations --
--------------------------------------------------------------------

module Semantics.Model.Example.TSets.Monad.Strength.Properties.Naturality where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.Model.Example.TSets.TSets
open import Semantics.Model.Example.TSets.Modality.Future
open import Semantics.Model.Example.TSets.Modality.Past
open import Semantics.Model.Example.TSets.Monad.Core
open import Semantics.Model.Example.TSets.Monad.Strength

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Naturality of the strength

strˢ-nat : ∀ {A A' B B' τ t}
         → (f : A →ᵗ A')
         → (g : B →ᵗ B')
         → (v : carrier ([ τ ]ᵒ A) t)
         → (c : Tˢ B τ t)
         → map-carrier (strᵀ {A'} {B'} ∘ᵗ mapˣᵗ ([ τ ]ᶠ f) (Tᶠ g)) (v , c)
         ≡ map-carrier (Tᶠ (mapˣᵗ f g) ∘ᵗ strᵀ {A} {B}) (v , c)
strˢ-nat {A} {A'} {B} {B'} {_} {t} f g v (leaf w) =
  cong leaf
    (cong (_, map-carrier g w)
      (sym (map-nat f (≤-reflexive (+-identityʳ t)) v)))
strˢ-nat {A} {A'} {B} {B'} {_} {t} f g v (op-node op w k k-nat) =
  dcong₂ (op-node op w)
    (ifun-ext (fun-ext (λ p → fun-ext (λ y →
      trans
        (cong₂ strˢ
          (sym (map-nat f _ _))
          refl)
        (strˢ-nat _ _ _ (k p y))))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
strˢ-nat {A} {A'} {B} {B'} {_} {t} f g v (delay-node τ k) =
  cong (delay-node τ)
    (trans
      (cong₂ strˢ
        (sym (map-nat f _ _))
        refl)
      (strˢ-nat _ _ _ k))

strᵀ-nat : ∀ {A A' B B' τ}
          → (f : A →ᵗ A')
          → (g : B →ᵗ B')
          →  strᵀ {A'} {B'} ∘ᵗ mapˣᵗ ([ τ ]ᶠ f) (Tᶠ g)
          ≡ᵗ Tᶠ (mapˣᵗ f g) ∘ᵗ strᵀ {A} {B}
strᵀ-nat {A} {A'} {B} {B'} {τ} f g =
  eqᵗ (λ vc →
    strˢ-nat f g (proj₁ vc) (proj₂ vc))
