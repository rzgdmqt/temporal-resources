---------------------------------
-- Monad on time-varying sets  --
---------------------------------

module Semantics.Model.Examples.TSets.Monad where

open import Semantics.Model.Monad

open import Semantics.Model.Examples.TSets.TSets

open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.Modality.Adjunction

open import Semantics.Model.Examples.TSets.BaseGroundTypes

open import Semantics.Model.Examples.TSets.Monad.Core
open import Semantics.Model.Examples.TSets.Monad.Effects
open import Semantics.Model.Examples.TSets.Monad.Effects.Algebraicity
open import Semantics.Model.Examples.TSets.Monad.Effects.Naturality
open import Semantics.Model.Examples.TSets.Monad.Strength
open import Semantics.Model.Examples.TSets.Monad.Strength.Algebraicity
open import Semantics.Model.Examples.TSets.Monad.Strength.Naturality
open import Semantics.Model.Examples.TSets.Monad.Handling

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Packaging the monad up in the model

TSetMon : Monad TSetCat TSetFut TSetTyp
TSetMon = record
        { Tᵒ                       = Tᵒ
        ; Tᶠ                       = Tᶠ
        ; ηᵀ                       = ηᵀ
        ; μᵀ                       = μᵀ
        ; τ-substᵀ                 = τ-substᵀ
        ; Tᶠ-idᵐ                   = ≡ᵗ-≡ (Tᶠ-idᵗ)
        ; Tᶠ-∘ᵐ                    = λ g f → ≡ᵗ-≡ (Tᶠ-∘ᵗ g f)
        ; ηᵀ-nat                   = λ f → ≡ᵗ-≡ (ηᵀ-nat f)
        ; μᵀ-nat                   = λ f → ≡ᵗ-≡ (μᵀ-nat f)
        ; μᵀ-identity₁             = ≡ᵗ-≡ μᵀ-identity₁
        ; μᵀ-identity₂             = ≡ᵗ-≡ μᵀ-identity₂
        ; μᵀ-assoc                 = ≡ᵗ-≡ μᵀ-assoc
        ; delayᵀ                   = delayᵀ
        ; opᵀ                      = opᵀ
        ; delayᵀ-nat               = λ τ f → ≡ᵗ-≡ (delayᵀ-nat τ f)
        ; opᵀ-nat                  = λ op f → ≡ᵗ-≡ (opᵀ-nat op f)
        ; delayᵀ-algebraicity      = λ τ → ≡ᵗ-≡ (delayᵀ-algebraicity τ)
        ; opᵀ-algebraicity         = λ op → ≡ᵗ-≡ (opᵀ-algebraicity op)
        ; strᵀ                     = strᵀ
        ; strᵀ-nat                 = λ f g → ≡ᵗ-≡ (strᵀ-nat f g)
        ; strᵀ-delayᵀ-algebraicity = ≡ᵗ-≡ strᵀ-delayᵀ-algebraicity
        ; T-alg-of-handlerᵀ        = T-alg-of-handlerᵀ
        }
