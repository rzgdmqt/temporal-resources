------------------------------------------------------------
-- Strong graded monad equipped with algebraic operations --
------------------------------------------------------------

-- Note: A version of the monad that is not quotioned by
--       the delay equations (identity and composition)

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.BaseGroundTypes

module Semantics.Model.Monad (Cat : Category)
                             (Fut : Future Cat)
                             (Typ : BaseGroundTypes Cat Fut) where

open import Util.Equality
open import Util.Operations
open import Util.Time

open Category Cat
open Future Fut
open BaseGroundTypes Typ

record Monad : Set₁ where

  field

    -- MONAD STRUCTURE

    -- Functor
    
    Tᵒ : TSet → Time → TSet
    Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ

    -- Unit and multiplication

    ηᵀ : ∀ {A} → A →ᵗ Tᵒ A 0
    μᵀ : ∀ {A τ τ'} → Tᵒ (Tᵒ A τ') τ →ᵗ Tᵒ A (τ + τ')

    -- Equality coercion/substitutions

    τ-substᵀ : ∀ {A τ τ'} → τ ≡ τ' → Tᵒ A τ →ᵗ Tᵒ A τ'

    -- Functoriality

    Tᶠ-idᵗ : ∀ {A τ} → Tᶠ {A} {A} {τ} idᵗ ≡ᵗ idᵗ
    Tᶠ-∘ᵗ : ∀ {A B C τ} → (g : B →ᵗ C) → (f : A →ᵗ B)
          → Tᶠ {A} {C} {τ} (g ∘ᵗ f) ≡ᵗ Tᶠ g ∘ᵗ Tᶠ f

    -- Unit and multiplication are natural

    ηᵀ-nat : ∀ {A B} → (f : A →ᵗ B) → ηᵀ ∘ᵗ f ≡ᵗ Tᶠ f ∘ᵗ ηᵀ
    μᵀ-nat : ∀ {A B τ τ'} → (f : A →ᵗ B) → μᵀ {τ = τ} {τ' = τ'} ∘ᵗ Tᶠ (Tᶠ f) ≡ᵗ Tᶠ f ∘ᵗ μᵀ

    -- Graded monad laws

    μᵀ-identity₁ : ∀ {A τ} →  μᵀ {τ = 0} {τ' = τ} ∘ᵗ ηᵀ {Tᵒ A τ} ≡ᵗ idᵗ
    μᵀ-identity₂ : ∀ {A τ} →  μᵀ {τ = τ} {τ' = 0} ∘ᵗ Tᶠ (ηᵀ {A}) ≡ᵗ τ-substᵀ (sym (+-identityʳ τ))
    μᵀ-assoc : ∀ {A τ τ' τ''} →  μᵀ {A} {τ} {τ' + τ''} ∘ᵗ Tᶠ μᵀ ≡ᵗ τ-substᵀ (+-assoc τ τ' τ'') ∘ᵗ (μᵀ ∘ᵗ μᵀ)

    -- EFFECTS

    -- Operations

    delayᵀ : ∀ {A} (τ : Time) {τ'} → [ τ ]ᵒ (Tᵒ A τ') →ᵗ Tᵒ A (τ + τ')
    opᵀ : ∀ {A τ} → (op : Op)
        → ⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ) →ᵗ Tᵒ A (op-time op + τ)

    -- Operations are natural

    delayᵀ-nat : ∀ {A B} (τ : Time) {τ'} → (f : A →ᵗ B)
               →  delayᵀ τ {τ' = τ'} ∘ᵗ [ τ ]ᶠ (Tᶠ f) ≡ᵗ Tᶠ f ∘ᵗ delayᵀ τ
    opᵀ-nat : ∀ {A B τ} → (op : Op) → (f : A →ᵗ B)
            →  opᵀ {τ = τ} op ∘ᵗ mapˣᵗ idᵗ ([ op-time op ]ᶠ (map⇒ᵗ idᵗ (Tᶠ f))) ≡ᵗ Tᶠ f ∘ᵗ opᵀ op

    -- Operations are algebraic

    delayᵀ-algebraicity : ∀ {A} (τ : Time) {τ' τ''}
                        → μᵀ {A} {τ + τ'} {τ''} ∘ᵗ delayᵀ τ {τ'}
                       ≡ᵗ τ-substᵀ (sym (+-assoc τ τ' τ'')) ∘ᵗ delayᵀ τ ∘ᵗ [ τ ]ᶠ (μᵀ {A} {τ'} {τ''})
    opᵀ-algebraicity : ∀ {A τ τ'} → (op : Op)
                     → μᵀ {A} {op-time op + τ} {τ'} ∘ᵗ opᵀ {τ = τ} op
                    ≡ᵗ τ-substᵀ (sym (+-assoc (op-time op) τ τ')) ∘ᵗ opᵀ op ∘ᵗ mapˣᵗ idᵗ ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ))

    -- STRENGTH

    -- Strength

    strᵀ : ∀ {A B τ} → [ τ ]ᵒ A ×ᵗ Tᵒ B τ →ᵗ Tᵒ (A ×ᵗ B) τ

    -- Strength is natural
    
    strᵀ-nat : ∀ {A A' B B' τ} → (f : A →ᵗ A') → (g : B →ᵗ B')
             → strᵀ {A'} {B'} ∘ᵗ mapˣᵗ ([ τ ]ᶠ f) (Tᶠ g) ≡ᵗ Tᶠ (mapˣᵗ f g) ∘ᵗ strᵀ {A} {B}
    
    -- Operations are algebraic wrt strength

    strᵀ-delayᵀ-algebraicity : ∀ {A B τ τ'}
                             → strᵀ {A} {B} {τ + τ'} ∘ᵗ mapˣᵗ idᵗ ((delayᵀ τ {τ'}))
                            ≡ᵗ delayᵀ τ ∘ᵗ [ τ ]ᶠ (strᵀ {A} {B} {τ'}) ∘ᵗ []-monoidal ∘ᵗ mapˣᵗ (δ {A} {τ} {τ'}) idᵗ

    -- strᵀ-opᵀ-algebraicity : (TODO)

    -- EFFECT HANDLING

    -- Turning an object of operation clauses to a T-algebra

    T-alg-of-handlerᵀ : ∀ {A τ τ'}
                      → Π Op (λ op → Π Time (λ τ'' →
                         ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                           ⇒ᵗ Tᵒ A (op-time op + τ'')))
                      →ᵗ Tᵒ (Tᵒ A τ') τ ⇒ᵗ Tᵒ A (τ + τ')

    -- Properties

    -- TODO
