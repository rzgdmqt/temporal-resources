---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.TSets
open import Semantics.Modality.Future
open import Semantics.Modality.Past

open import Util.HProp
open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Monad where

-- Interpretation of ground types as sets

⟦_⟧ᵍ : GType → TSet
⟦ Base B ⟧ᵍ   = ConstTSet (BaseSet B)
⟦ Unit ⟧ᵍ     = 𝟙ᵗ
⟦ Empty ⟧ᵍ    = 𝟘ᵗ
⟦ [ τ ]ᵍ A ⟧ᵍ = [ τ ]ᵒ ⟦ A ⟧ᵍ

-- The free graded monad generated by the operations in Op

-- TODO: work out the formal details of the corresponding
--       definitions (postulating them for time being)

postulate

  -- Object-mapping

  Tᵒ : TSet → Time → TSet

  -- Functorial action

  Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ

  -- Monotonicity wrt. gradings

  T-≤τ : ∀ {A τ τ'} → τ ≤ τ' → Tᵒ A τ →ᵗ Tᵒ A τ'

  -- T is a [_]-module  

  T-[]-module : ∀ {A τ τ'} → [ τ ]ᵒ (Tᵒ A τ') →ᵗ Tᵒ A (τ + τ')

  -- Unit

  ηᵀ : ∀ {A} → A →ᵗ Tᵒ A 0

  -- Multiplication

  μᵀ : ∀ {A τ τ'} → Tᵒ (Tᵒ A τ') τ →ᵗ Tᵒ A (τ + τ')

  -- Strength

  strᵀ : ∀ {A B τ τ'} → [ τ ]ᵒ (⟨ τ' ⟩ᵒ A) ×ᵗ Tᵒ B τ →ᵗ Tᵒ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ

  -- Algebraic operations

  opᵀ : ∀ {A τ} → (op : Op)
      → ⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ) →ᵗ Tᵒ A (op-time op + τ)

  -- T-algebra induced by an effect handler

  alg-of-handler : ∀ {A τ τ'}
                 → Π Op (λ op → Π Time (λ τ'' →
                    ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                      ⇒ᵗ Tᵒ A (op-time op + τ'')))
                 →ᵗ Tᵒ (Tᵒ A τ') τ ⇒ᵗ (Tᵒ A (τ + τ'))
