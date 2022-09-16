---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

module Semantics.Model.Examples.TSets.Monad.Effects.Algebraicity where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.Model.Examples.TSets.TSets
open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.Monad.Core
open import Semantics.Model.Examples.TSets.Monad.Effects

open import Util.Equality
open import Util.Operations
open import Util.Time

-- The (algebraic) operations of the monad generated by the operations in Op (continued)
----------------------------------------------------------------------------------------

-- Algebraicity of the delay operation

delayᵀ-algebraicity : ∀ {A} (τ : Time) {τ' τ''}
                    →     μᵀ {A} {τ + τ'} {τ''}
                       ∘ᵗ delayᵀ τ {τ'}
                    ≡ᵗ    τ-substᵀ (sym (+-assoc τ τ' τ''))
                       ∘ᵗ delayᵀ τ
                       ∘ᵗ [ τ ]ᶠ (μᵀ {A} {τ'} {τ''})
delayᵀ-algebraicity {A} τ {τ'} {τ''} =
  eqᵗ (λ {t} c → refl)


-- Algebraicity of the (other) algebraic operations

opᵀ-algebraicity : ∀ {A τ τ'} → (op : Op)
                 →     μᵀ {A} {op-time op + τ} {τ'}
                    ∘ᵗ opᵀ {τ = τ} op
                 ≡ᵗ    τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
                    ∘ᵗ opᵀ op
                    ∘ᵗ mapˣᵗ idᵗ ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ))
opᵀ-algebraicity {A} {τ} {τ'} op =
  eqᵗ (λ {t} c → refl)
