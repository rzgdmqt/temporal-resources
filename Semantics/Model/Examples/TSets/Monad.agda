{-# OPTIONS --experimental-lossy-unification #-}

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
open import Semantics.Model.Examples.TSets.Monad.Effects.Properties.Algebraicity
open import Semantics.Model.Examples.TSets.Monad.Effects.Properties.Naturality
open import Semantics.Model.Examples.TSets.Monad.Strength
open import Semantics.Model.Examples.TSets.Monad.Strength.Properties.Algebraicity
open import Semantics.Model.Examples.TSets.Monad.Strength.Properties.Naturality
open import Semantics.Model.Examples.TSets.Monad.Strength.Properties.UnitMultiplication
open import Semantics.Model.Examples.TSets.Monad.Strength.Properties.CartesianStructure
open import Semantics.Model.Examples.TSets.Monad.Handling
open import Semantics.Model.Examples.TSets.Monad.Handling.Properties.Delay

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Packaging the monad up in the model

TSetMon : Monad TSetCat TSetFut TSetPas TSetAdj TSetTyp
TSetMon = record
        { Tᵒ                       = Tᵒ
        ; Tᶠ                       = λ {A} {B} {τ} → Tᶠ {A} {B} {τ}
        ; ηᵀ                       = λ {A} → ηᵀ {A}
        ; μᵀ                       = λ {A} {τ} {τ'} → μᵀ {A} {τ} {τ'}
        ; τ-substᵀ                 = λ {A} {τ} {τ'} → τ-substᵀ {A} {τ} {τ'}
        ; τ-substᵀ-refl            = λ {A} {τ} → ≡ᵗ-≡ (τ-substᵀ-refl {A} {τ})
        ; τ-substᵀ-trans           = λ {A} {τ} {τ'} {τ''} p q → ≡ᵗ-≡ (τ-substᵀ-trans {A} {τ} {τ'} {τ''} p q)
        ; T-idᵐ                    = λ {A} {τ} → ≡ᵗ-≡ (Tᶠ-idᵗ {A} {τ})
        ; T-∘ᵐ                     = λ {A} {B} {C} {τ} g f → ≡ᵗ-≡ (Tᶠ-∘ᵗ {A} {B} {C} {τ} g f)
        ; ηᵀ-nat                   = λ {A} {B} f → ≡ᵗ-≡ (ηᵀ-nat {A} {B} f)
        ; μᵀ-nat                   = λ {A} {B} {τ} {τ'} f → ≡ᵗ-≡ (μᵀ-nat {A} {B} {τ} {τ'} f)
        ; T-μ∘η≡id                 = λ {A} {τ} → ≡ᵗ-≡ (μᵀ-identity₁ {A} {τ})
        ; T-μ∘Tη≡id                = λ {A} {τ} → ≡ᵗ-≡ (μᵀ-identity₂ {A} {τ})
        ; T-μ∘μ≡μ∘Tμ               = λ {A} {τ} {τ'} {τ''} → ≡ᵗ-≡ (μᵀ-assoc {A} {τ} {τ'} {τ''})
        ; delayᵀ                   = λ {A} τ {τ'} → delayᵀ {A} τ {τ'}
        ; opᵀ                      = {!!} --λ {A} {τ} op → opᵀ {A} {τ} op
        ; delayᵀ-nat               = λ {A} {B} τ {τ'} f → ≡ᵗ-≡ (delayᵀ-nat {A} {B} τ {τ'} f)
        ; opᵀ-nat                  = {!!} --λ {A} {B} {τ} op f → ≡ᵗ-≡ (opᵀ-nat {A} {B} {τ} op f)
        ; delayᵀ-algebraicity      = λ {A} τ {τ'} {τ''} → ≡ᵗ-≡ (delayᵀ-algebraicity {A} τ {τ'} {τ''})
        ; opᵀ-algebraicity         = {!!} --λ {A} {τ} {τ'} op → ≡ᵗ-≡ (opᵀ-algebraicity {A} {τ} {τ'} op)
        ; strᵀ                     = {!!} --strᵀ
        ; strᵀ-nat                 = {!!} --λ f g → ≡ᵗ-≡ (strᵀ-nat f g)
        ; strᵀ-ηᵀ                  = {!!} --λ {A} {B} → ≡ᵗ-≡ (strᵀ-ηᵀ {A} {B})
        ; strᵀ-μᵀ                  = {!!} --λ {A} {B} → ≡ᵗ-≡ (strᵀ-μᵀ {A} {B})
        ; strᵀ-sndᵐ                = {!!} --λ {A} {B} → ≡ᵗ-≡ (strᵀ-sndᵗ {A} {B})
        ; strᵀ-assoc               = {!!} --λ {A} {B} {C} → ≡ᵗ-≡ (strᵀ-assoc {A} {B} {C})
        ; strᵀ-delayᵀ-algebraicity = {!!} --≡ᵗ-≡ strᵀ-delayᵀ-algebraicity
        ; strᵀ-opᵀ-algebraicity    = {!!} --{!!}
        ; T-alg-of-handlerᵀ        = λ {A} {τ} {τ'} → T-alg-of-handlerᵀ {A} {τ} {τ'}
        ; T-alg-of-handlerᵀ-ηᵀ     = {!!} --{!!}
        ; T-alg-of-handlerᵀ-delayᵀ = {!!} --λ {A} {τ} {τ'} {τ''} → ≡ᵗ-≡ (T-alg-of-handlerᵀ-delayᵀ {A} {τ} {τ'} {τ''})
        ; T-alg-of-handlerᵀ-opᵀ    = {!!} --{!!}
        }
