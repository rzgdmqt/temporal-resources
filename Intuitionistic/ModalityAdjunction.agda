---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

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
open import ComonadModality
open import MonadModality

module ModalityAdjunction where

η⊣ : ∀ {A τ} → A →ᵗ [ τ ]ᵒ (⟨ τ ⟩ᵒ A)
η⊣ {tset A Af} {τ} =
  tset-map
    (λ {t'} a → m≤n+m τ t' , Af (≤-reflexive (sym (m+n∸n≡m t' τ))) a)

ε⊣ : ∀ {A τ} → ⟨ τ ⟩ᵒ ([ τ ]ᵒ A) →ᵗ A
ε⊣ {tset A Af} {τ} =
  tset-map
    (λ { {t'} (p , a) → Af (n≤m⇒m∸n+n≤m τ t' p) a })
