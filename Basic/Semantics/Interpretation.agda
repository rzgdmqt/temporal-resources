-------------------------------------------------------------
-- Interpretation of well-typed terms in time-varying sets --
-------------------------------------------------------------

open import Function

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Semantics.TSets
open import Semantics.Monad

open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Modality.Adjunction

open import Util.Operations
open import Util.Time

module Semantics.Interpretation where

-- Interpretation of value and computation types

mutual

  ⟦_⟧ᵛ : VType → TSet
  ⟦ Base B ⟧ᵛ  = ConstTSet (BaseSet B)
  ⟦ Unit ⟧ᵛ    = 𝟙ᵗ
  ⟦ Empty ⟧ᵛ   = 𝟘ᵗ
  ⟦ A ⇒ C ⟧ᵛ   = ⟦ A ⟧ᵛ ⇒ᵗ ⟦ C ⟧ᶜ
  ⟦ [ τ ] A ⟧ᵛ = [ τ ]ᵒ ⟦ A ⟧ᵛ

  ⟦_⟧ᶜ : CType → TSet
  ⟦ A ‼ τ ⟧ᶜ = Tᵒ ⟦ A ⟧ᵛ τ

  infix 25 ⟦_⟧ᵛ
  infix 25 ⟦_⟧ᶜ

-- Relating the interpretation of ground types and ground type to type conversion

⟦⟧ᵛ-⟦⟧ᵍ : (B : GType) → ⟦ type-of-gtype B ⟧ᵛ →ᵗ ConstTSet ⟦ B ⟧ᵍ
⟦⟧ᵛ-⟦⟧ᵍ (Base B) = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ Unit     = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ Empty    = idᵗ

⟦⟧ᵍ-⟦⟧ᵛ : (B : GType) → ConstTSet ⟦ B ⟧ᵍ →ᵗ ⟦ type-of-gtype B ⟧ᵛ
⟦⟧ᵍ-⟦⟧ᵛ (Base B) = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ Unit     = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ Empty    = idᵗ

-- Interpretation of contexts as environments

⟦_⟧ᵉ : Ctx → TSet
⟦ [] ⟧ᵉ      = 𝟙ᵗ
⟦ Γ ∷ A ⟧ᵉ   = ⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ
⟦ Γ ⟨ τ ⟩ ⟧ᵉ = ⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ

infix 25 ⟦_⟧ᵉ

-- Total time-passage of an environment as a single ⟨_⟩ modality

split-env-⟨⟩ : ∀ {Γ Γ' Γ''} → Γ' , Γ'' split Γ → ⟦ Γ ⟧ᵉ →ᵗ ⟨ ctx-time Γ'' ⟩ᵒ ⟦ Γ' ⟧ᵉ
split-env-⟨⟩ split-[]    = η
split-env-⟨⟩ (split-∷ p) = split-env-⟨⟩ p ∘ᵗ fstᵗ
split-env-⟨⟩ {Γ' = Γ'} {Γ'' = Γ'' ⟨ τ ⟩} (split-⟨⟩ p) =
     ⟨⟩-≤ {A = ⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (ctx-time Γ'') τ))
  ∘ᵗ μ {A = ⟦ Γ' ⟧ᵉ}
  ∘ᵗ ⟨ τ ⟩ᶠ (split-env-⟨⟩ p)

-- Projecting a variable out of an environment

var-in-env : ∀ {Γ A τ} → A ∈[ τ ] Γ → ⟦ Γ ⟧ᵉ →ᵗ ⟨ τ ⟩ᵒ ⟦ A ⟧ᵛ
var-in-env {A = A} Hd                = η ∘ᵗ sndᵗ
var-in-env {A = A} (Tl-∷ x)          = var-in-env x ∘ᵗ fstᵗ
var-in-env {A = A} (Tl-⟨⟩ {τ = τ} x) = μ {A = ⟦ A ⟧ᵛ} ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x)

-- Interpretation of well-typed value and computation terms

mutual

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → Γ ⊢V⦂ A → ⟦ Γ ⟧ᵉ →ᵗ ⟦ A ⟧ᵛ
  
  ⟦ var x ⟧ᵛᵗ = ε-⟨⟩ ∘ᵗ var-in-env x
  
  ⟦ const c ⟧ᵛᵗ = constᵗ c ∘ᵗ terminalᵗ
  
  ⟦ ⋆ ⟧ᵛᵗ = terminalᵗ
  
  ⟦ lam M ⟧ᵛᵗ = curryᵗ ⟦ M ⟧ᶜᵗ
  
  ⟦ box {τ = τ} V ⟧ᵛᵗ = ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ) ∘ᵗ η⊣ 

  infix 25 ⟦_⟧ᵛᵗ


  ⟦_⟧ᶜᵗ : ∀ {Γ C} → Γ ⊢C⦂ C → ⟦ Γ ⟧ᵉ →ᵗ ⟦ C ⟧ᶜ
  
  ⟦ return V ⟧ᶜᵗ = ηᵀ ∘ᵗ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (_;_ {τ = τ} M N) =
       μᵀ
    ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵗ strᵀ {A = ⟦ Γ ⟧ᵉ} {τ' = τ} 
    ∘ᵗ ⟨ η⊣ {A = ⟦ Γ ⟧ᵉ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ

  ⟦ V · W ⟧ᶜᵗ = appᵗ ∘ᵗ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵗ
  
  ⟦ absurd V ⟧ᶜᵗ = initialᵗ ∘ᵗ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {τ} op V M) =
    let f : ⟨ op-time op ⟩ᵒ (⟦ Γ ⟧ᵉ ×ᵗ ConstTSet ⟦ arity op ⟧ᵍ) →ᵗ Tᵒ ⟦ A ⟧ᵛ τ
        f = ⟦ M ⟧ᶜᵗ ∘ᵗ mapˣᵗ idᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) ∘ᵗ costr-⟨⟩ {A = ⟦ Γ ⟧ᵉ} in
    let g : ⟦ Γ ⟧ᵉ ×ᵗ ConstTSet ⟦ arity op ⟧ᵍ →ᵗ [ op-time op ]ᵒ (Tᵒ ⟦ A ⟧ᵛ τ)
        g = [ op-time op ]ᶠ f ∘ᵗ η⊣ in
    opᵀ op ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ,
                curryᵗ g ⟩ᵗ

  ⟦ handle M `with H `in N ⟧ᶜᵗ = {!!}

  ⟦ unbox {Γ'} {τ = τ} p q V M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵗ ⟨ idᵗ ,
                    ε⊣
                 ∘ᵗ (⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ)
                 ∘ᵗ ⟨⟩-≤ {A = ⟦ Γ' ⟧ᵉ} q
                 ∘ᵗ split-env-⟨⟩ p ⟩ᵗ

  ⟦ delay τ refl M ⟧ᶜᵗ =
       T-≤τ (≤-reflexive (+-comm τ _))
    ∘ᵗ T-[]-module ∘ᵗ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ)
    ∘ᵗ η⊣ 

  infix 25 ⟦_⟧ᶜᵗ

