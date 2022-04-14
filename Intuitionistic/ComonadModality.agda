------------------------------------------------------------------
-- Semantics of the type modality `[ t ] A` as a graded comonad --
------------------------------------------------------------------

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
open import TSets

module ComonadModality where

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
