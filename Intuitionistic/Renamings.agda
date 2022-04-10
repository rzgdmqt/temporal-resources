------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language

module Renamings where

-- Renamings

data Ren : Ctx → Ctx → Set where
  ∅      : ∀ {Γ} → Ren [] Γ
  wk     : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren Γ (Γ' ∷ᶜ A)
  ext    : ∀ {Γ Γ' A} → Ren Γ Γ' → A ∈ Γ' → Ren (Γ ∷ᶜ A) Γ'
  ⟨⟩-mon : ∀ {Γ Γ' τ τ'} → Ren Γ Γ' → τ' ≤ τ → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ' ⟩)
  ⟨⟩-eta : ∀ {Γ Γ'} → Ren Γ Γ' → Ren (Γ ⟨ 0 ⟩) Γ' 
  ⟨⟩-mu  : ∀ {Γ Γ' τ τ'} → Ren Γ Γ' → Ren (Γ ⟨ τ + τ' ⟩) (Γ' ⟨ τ ⟩ ⟨ τ' ⟩)

-- Renaming a variable

var-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → A ∈ Γ
           ------------
           → A ∈ Γ'

var-rename (wk ρ)    Hd     = Tl (var-rename ρ Hd)
var-rename (ext ρ x) Hd     = x
var-rename (wk ρ)    (Tl x) = Tl (var-rename ρ (Tl x))
var-rename (ext ρ _) (Tl x) = var-rename ρ x

-- Identity renaming

idʳ : ∀ {Γ} → Ren Γ Γ
idʳ {[]}      = ∅
idʳ {Γ ∷ᶜ A}  = ext (wk idʳ) Hd
idʳ {Γ ⟨ τ ⟩} = ⟨⟩-mon idʳ ≤-refl

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''

ρ' ∘ʳ ∅ = ∅

wk ρ' ∘ʳ wk ρ = wk (ρ' ∘ʳ wk ρ)
ext ρ' x ∘ʳ wk ρ = ρ' ∘ʳ ρ

ρ' ∘ʳ ext ρ x = ext (ρ' ∘ʳ ρ) (var-rename ρ' x)

wk ρ' ∘ʳ ⟨⟩-mon ρ p = wk (ρ' ∘ʳ ⟨⟩-mon ρ p)
⟨⟩-mon ρ' q ∘ʳ ⟨⟩-mon ρ p = ⟨⟩-mon (ρ' ∘ʳ ρ) (≤-trans q p)
⟨⟩-eta ρ' ∘ʳ ⟨⟩-mon ρ p = {!ρ' ∘ʳ ρ!}
⟨⟩-mu ρ' ∘ʳ ⟨⟩-mon ρ p = {!ρ' ∘ʳ ρ!}

ρ' ∘ʳ ⟨⟩-eta ρ   = ⟨⟩-eta (ρ' ∘ʳ ρ)

wk ρ' ∘ʳ ⟨⟩-mu ρ = {!!}
⟨⟩-mon ρ' q ∘ʳ ⟨⟩-mu ρ = {!!}
⟨⟩-eta ρ' ∘ʳ ⟨⟩-mu ρ = {!!}
⟨⟩-mu ρ' ∘ʳ ⟨⟩-mu ρ = {!!}
