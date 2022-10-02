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

TSetMon : Monad TSetCat TSetFut TSetPas TSetAdj TSetTyp
TSetMon = record
        { Tᵒ                       = Tᵒ
        ; Tᶠ                       = Tᶠ
        ; ηᵀ                       = ηᵀ
        ; μᵀ                       = μᵀ
        ; τ-substᵀ                 = τ-substᵀ
        ; τ-substᵀ-refl            = ≡ᵗ-≡ (τ-substᵀ-refl)
        ; τ-substᵀ-trans           = λ p q → ≡ᵗ-≡ (τ-substᵀ-trans p q)
        ; T-idᵐ                    = ≡ᵗ-≡ (Tᶠ-idᵗ)
        ; T-∘ᵐ                     = λ g f → ≡ᵗ-≡ (Tᶠ-∘ᵗ g f)
        ; ηᵀ-nat                   = λ f → ≡ᵗ-≡ (ηᵀ-nat f)
        ; μᵀ-nat                   = λ f → ≡ᵗ-≡ (μᵀ-nat f)
        ; T-μ∘η≡id                 = ≡ᵗ-≡ μᵀ-identity₁
        ; T-μ∘Tη≡id                = ≡ᵗ-≡ μᵀ-identity₂
        ; T-μ∘μ≡μ∘Tμ               = ≡ᵗ-≡ μᵀ-assoc
        ; delayᵀ                   = delayᵀ
        ; opᵀ                      = opᵀ
        ; delayᵀ-nat               = λ τ f → ≡ᵗ-≡ (delayᵀ-nat τ f)
        ; opᵀ-nat                  = λ op f → ≡ᵗ-≡ (opᵀ-nat op f)
        ; delayᵀ-algebraicity      = λ τ → ≡ᵗ-≡ (delayᵀ-algebraicity τ)
        ; opᵀ-algebraicity         = λ op → ≡ᵗ-≡ (opᵀ-algebraicity op)
        ; strᵀ                     = strᵀ
        ; strᵀ-nat                 = λ f g → ≡ᵗ-≡ (strᵀ-nat f g)
        ; strᵀ-ηᵀ                  = {!!}
        ; strᵀ-μᵀ                  = {!!}
        ; strᵀ-sndᵐ                = {!!}
        ; strᵀ-assoc               = {!!}
        ; strᵀ-delayᵀ-algebraicity = ≡ᵗ-≡ strᵀ-delayᵀ-algebraicity
        ; strᵀ-opᵀ-algebraicity    = {!!}
        ; T-alg-of-handlerᵀ        = T-alg-of-handlerᵀ
        ; T-alg-of-handlerᵀ-ηᵀ     = {!!}
        ; T-alg-of-handlerᵀ-delayᵀ = {!!}
        ; T-alg-of-handlerᵀ-opᵀ    = {!!}
        }
