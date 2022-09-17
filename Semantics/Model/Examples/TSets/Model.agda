-------------------------------------------------------
-- Model of the language based on time-varying sets  --
-------------------------------------------------------

module Semantics.Model.Examples.TSets.Model where

open import Semantics.Model
open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction
open import Semantics.Model.BaseGroundTypes
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

-- Category part of the model

Cat : Category
Cat = record
        { Obj              = TSet
        ; _→ᵐ_             = _→ᵗ_
        ; idᵐ              = idᵗ
        ; _∘ᵐ_             = _∘ᵗ_
        ; ∘ᵐ-identityˡ     = λ f → ≡ᵗ-≡ (∘ᵗ-identityˡ f)
        ; ∘ᵐ-identityʳ     = λ f → ≡ᵗ-≡ (∘ᵗ-identityʳ f)
        ; ∘ᵐ-assoc         = λ h g f → ≡ᵗ-≡ (∘ᵗ-assoc h g f)
        ; 𝟙ᵐ               = 𝟙ᵗ
        ; terminalᵐ        = terminalᵗ
        ; terminalᵐ-unique = ≡ᵗ-≡ terminalᵗ-unique
        ; 𝟘ᵐ               = 𝟘ᵗ
        ; initialᵐ         = initialᵗ
        ; initialᵐ-unique  = ≡ᵗ-≡ initialᵗ-unique
        ; _×ᵐ_             = _×ᵗ_
        ; fstᵐ             = fstᵗ
        ; sndᵐ             = sndᵗ
        ; ⟨_,_⟩ᵐ           = ⟨_,_⟩ᵗ
        ; ⟨⟩ᵐ-fstᵐ         = λ f g → ≡ᵗ-≡ (⟨⟩ᵗ-fstᵗ f g)
        ; ⟨⟩ᵐ-sndᵐ         = λ f g → ≡ᵗ-≡ (⟨⟩ᵗ-sndᵗ f g)
        ; ⟨⟩ᵐ-unique       = λ f g h p q → ≡ᵗ-≡ (⟨⟩ᵗ-unique f g h (≡-≡ᵗ p) (≡-≡ᵗ q))
        ; Π                = Πᵗ
        ; projᵐ            = projᵗ
        ; ⟨_⟩ᵢᵐ            = ⟨_⟩ᵢᵗ
        ; mapⁱˣᵐ-identity  = λ {I} {A} → ≡ᵗ-≡ (mapⁱˣᵗ-identity {I} {A})
        ; mapⁱˣᵐ-∘ᵐ        = λ f g → ≡ᵗ-≡ (mapⁱˣᵗ-∘ᵗ f g)
        ; ⟨⟩ᵢᵐ-projᵐ       = λ f i → ≡ᵗ-≡ (⟨⟩ᵢᵗ-projᵗ f i)
        ; ⟨⟩ᵢᵐ-∘ᵐ          = λ f g → ≡ᵗ-≡ (⟨⟩ᵢᵗ-∘ᵗ f g)
        ; _⇒ᵐ_             = _⇒ᵗ_
        ; appᵐ             = appᵗ
        ; map⇒ᵐ            = map⇒ᵗ
        ; curryᵐ           = curryᵗ
        ; uncurryᵐ         = uncurryᵗ
        ; map⇒ᵐ-identity   = ≡ᵗ-≡ map⇒ᵗ-identity
        ; curryᵐ-mapˣᵐ     = λ f g h → ≡ᵗ-≡ (curryᵗ-mapˣᵗ f g h)
        ; uncurryᵐ-mapˣᵐʳ  = λ f g → ≡ᵗ-≡ (uncurryᵗ-mapˣᵗʳ f g)
        }

-- Future modality part of the model

Fut : Future Cat
Fut = record
        { [_]ᵒ          = [_]ᵒ
        ; [_]ᶠ          = [_]ᶠ
        ; []-≤          = λ {A} → []-≤ {A}
        ; ε             = ε
        ; ε⁻¹           = ε⁻¹
        ; δ             = λ {A} → δ {A}
        ; δ⁻¹           = λ {A} → δ⁻¹ {A}
        ; []-idᵐ        = λ {A} → ≡ᵗ-≡ ([]-idᵗ {A})
        ; []-∘ᵐ         = λ f g → ≡ᵗ-≡ ([]-∘ᵗ f g)
        ; []-≤-nat      = λ f p → ≡ᵗ-≡ ([]-≤-nat f p)
        ; []-≤-refl     = λ {A} → ≡ᵗ-≡ ([]-≤-refl {A})
        ; []-≤-trans    = λ {A} p q → ≡ᵗ-≡ ([]-≤-trans {A} p q)
        ; []-ε-nat      = λ f → ≡ᵗ-≡ ([]-ε-nat f)
        ; []-ε⁻¹-nat    = λ f → ≡ᵗ-≡ ([]-ε⁻¹-nat f)
        ; []-δ-nat      = λ f → ≡ᵗ-≡ ([]-δ-nat f)
        ; []-δ⁻¹-nat    = λ f → ≡ᵗ-≡ ([]-δ⁻¹-nat f)
        ; []-δ-≤        = λ {A} p q → ≡ᵗ-≡ ([]-δ-≤ {A} p q)
        ; []-ε∘ε⁻¹≡id   = λ {A} → ≡ᵗ-≡ ([]-ε∘ε⁻¹≡id {A})
        ; []-ε⁻¹∘ε≡id   = λ {A} → ≡ᵗ-≡ ([]-ε⁻¹∘ε≡id {A})
        ; []-δ∘δ⁻¹≡id   = λ {A} → ≡ᵗ-≡ ([]-δ∘δ⁻¹≡id {A})
        ; []-δ⁻¹∘δ≡id   = λ {A} → ≡ᵗ-≡ ([]-δ⁻¹∘δ≡id {A})
        ; []-ε∘δ≡id     = λ {A} → ≡ᵗ-≡ ([]-ε∘δ≡id {A})
        ; []-Dε∘δ≡≤     = λ {A} → ≡ᵗ-≡ ([]-Dε∘δ≡≤ {A})
        ; []-δ∘δ≡Dδ∘δ∘≤ = λ {A} → ≡ᵗ-≡ ([]-δ∘δ≡Dδ∘δ∘≤ {A})
        ; []-monoidal   = λ {A} {B} → []-monoidal {A} {B}
        }

-- Past modality part of the model

Pas : Past Cat
Pas = record
        { ⟨_⟩ᵒ           = ⟨_⟩ᵒ
        ; ⟨_⟩ᶠ           = ⟨_⟩ᶠ
        ; ⟨⟩-≤           = λ {A} → ⟨⟩-≤ {A}
        ; η              = η
        ; η⁻¹            = η⁻¹
        ; μ              = λ {A} → μ {A}
        ; μ⁻¹            = λ {A} → μ⁻¹ {A}
        ; ⟨⟩-idᵐ         = λ {A} → ≡ᵗ-≡ (⟨⟩-idᵗ {A})
        ; ⟨⟩-∘ᵐ          = λ f g → ≡ᵗ-≡ (⟨⟩-∘ᵗ f g)
        ; ⟨⟩-≤-nat       = λ f p → ≡ᵗ-≡ (⟨⟩-≤-nat f p)
        ; ⟨⟩-≤-refl      = λ {A} → ≡ᵗ-≡ (⟨⟩-≤-refl {A})
        ; ⟨⟩-≤-trans     = λ {A} p q → ≡ᵗ-≡ (⟨⟩-≤-trans {A} p q)
        ; ⟨⟩-η-nat       = λ f → ≡ᵗ-≡ (⟨⟩-η-nat f)
        ; ⟨⟩-η⁻¹-nat     = λ f → ≡ᵗ-≡ (⟨⟩-η⁻¹-nat f)
        ; ⟨⟩-μ-nat       = λ f → ≡ᵗ-≡ (⟨⟩-μ-nat f)
        ; ⟨⟩-μ⁻¹-nat     = λ f → ≡ᵗ-≡ (⟨⟩-μ⁻¹-nat f)
        ; ⟨⟩-μ-≤         = λ {A} p q → ≡ᵗ-≡ (⟨⟩-μ-≤ {A} p q)
        ; ⟨⟩-μ-≤₁        = λ {A} p → ≡ᵗ-≡ (⟨⟩-μ-≤₁ {A} p)
        ; ⟨⟩-μ-≤₂        = λ {A} p → ≡ᵗ-≡ (⟨⟩-μ-≤₂ {A} p)
        ; ⟨⟩-μ⁻¹-≤₂      = λ {A} p → ≡ᵗ-≡ (⟨⟩-μ⁻¹-≤₂ {A} p)
        ; ⟨⟩-η∘η⁻¹≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-η∘η⁻¹≡id {A})
        ; ⟨⟩-η⁻¹∘η≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-η⁻¹∘η≡id {A})
        ; ⟨⟩-μ∘μ⁻¹≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘μ⁻¹≡id {A})
        ; ⟨⟩-μ⁻¹∘μ≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-μ⁻¹∘μ≡id {A})
        ; ⟨⟩-μ∘η≡id      = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘η≡id {A})
        ; ⟨⟩-μ∘Tη≡id     = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘Tη≡id {A})
        ; ⟨⟩-μ∘μ≡≤∘μ∘Tμ  = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘μ≡≤∘μ∘Tμ {A})
        }

-- Modal adjunction part of the model

Adj : Adjunction Cat Fut Pas
Adj = record
        { η⊣       = η⊣
        ; ε⊣       = ε⊣
        ; η⊣-nat   = λ f → ≡ᵗ-≡ (η⊣-nat f)
        ; ε⊣-nat   = λ f → ≡ᵗ-≡ (ε⊣-nat f)
        ; ε⊣∘Fη≡id = λ {A} → ≡ᵗ-≡ (ε⊣∘Fη≡id {A})
        ; Gε⊣∘η≡id = λ {A} → ≡ᵗ-≡ (Gε⊣∘η≡id {A})
        ; η⊣≡ε⁻¹∘η = λ {A} → ≡ᵗ-≡ (η⊣≡ε⁻¹∘η {A})
        ; ε⊣≡ε∘η⁻¹ = λ {A} → ≡ᵗ-≡ (ε⊣≡ε∘η⁻¹ {A})
        }

-- Base and ground types interpretation part of the model

Typ : BaseGroundTypes Cat Fut
Typ = record
        { ConstObj = λ B → ConstTSet (BaseSet B)
        ; constᵐ   = λ c → constᵗ c
        }

-- Equality of two kinds of ground types interpretation
-- And rewriting their mentions in algebraic operations

open BaseGroundTypes Typ renaming (⟦_⟧ᵍ to ⟦_⟧ᵍᵗ)

⟦⟧ᵍ-≡ : (A : GType) → ⟦ A ⟧ᵍᵗ ≡ ⟦ A ⟧ᵍ
⟦⟧ᵍ-≡ (Base B) = refl
⟦⟧ᵍ-≡ Unit = refl
⟦⟧ᵍ-≡ Empty = refl
⟦⟧ᵍ-≡ ([ τ ]ᵍ A) = cong [ τ ]ᵒ (⟦⟧ᵍ-≡ A)

opᵀᵗ : ∀ {A τ} → (op : Op)
     → ⟦ param op ⟧ᵍᵗ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍᵗ ⇒ᵗ Tᵒ A τ) →ᵗ Tᵒ A (op-time op + τ)
opᵀᵗ op rewrite ⟦⟧ᵍ-≡ (param op) | ⟦⟧ᵍ-≡ (arity op) =
  opᵀ op

opᵀ-natᵗ : ∀ {A B τ} → (op : Op) → (f : A →ᵗ B)
         →  opᵀᵗ {τ = τ} op ∘ᵗ mapˣᵗ idᵗ ([ op-time op ]ᶠ (map⇒ᵗ idᵗ (Tᶠ f))) ≡ᵗ Tᶠ f ∘ᵗ opᵀᵗ op
opᵀ-natᵗ op f rewrite ⟦⟧ᵍ-≡ (param op) | ⟦⟧ᵍ-≡ (arity op) =
  opᵀ-nat op f

opᵀ-algebraicityᵗ : ∀ {A τ τ'} → (op : Op)
                  → μᵀ {A} {op-time op + τ} {τ'} ∘ᵗ opᵀᵗ {τ = τ} op
                 ≡ᵗ τ-substᵀ (sym (+-assoc (op-time op) τ τ')) ∘ᵗ opᵀᵗ op ∘ᵗ mapˣᵗ idᵗ ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ))
opᵀ-algebraicityᵗ op rewrite ⟦⟧ᵍ-≡ (param op) | ⟦⟧ᵍ-≡ (arity op) =
  opᵀ-algebraicity op

T-alg-of-handlerᵀᵗ : ∀ {A τ τ'}
                   → Πᵗ Op (λ op → Πᵗ Time (λ τ'' →
                      ⟦ param op ⟧ᵍᵗ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍᵗ ⇒ᵗ (Tᵒ A τ'')))
                        ⇒ᵗ Tᵒ A (op-time op + τ'')))
                   →ᵗ Tᵒ (Tᵒ A τ') τ ⇒ᵗ Tᵒ A (τ + τ')
T-alg-of-handlerᵀᵗ {A} {τ} {τ'} =
     T-alg-of-handlerᵀ
  ∘ᵗ mapⁱˣᵗ (λ op → mapⁱˣᵗ (λ τ'' →
       map⇒ᵗ
         (mapˣᵗ
           (subst (λ G → G →ᵗ ⟦ param op ⟧ᵍᵗ) (⟦⟧ᵍ-≡ (param op)) idᵗ)
           (subst (λ G → [ op-time op ]ᵒ (G ⇒ᵗ (Tᵒ A τ'')) →ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍᵗ ⇒ᵗ (Tᵒ A τ''))) (⟦⟧ᵍ-≡ (arity op)) idᵗ)) idᵗ))

-- Monad part of the model

Mon : Monad Cat Fut Typ
Mon = record
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
        ; opᵀ                      = opᵀᵗ
        ; delayᵀ-nat               = λ τ f → ≡ᵗ-≡ (delayᵀ-nat τ f)
        ; opᵀ-nat                  = λ op f → ≡ᵗ-≡ (opᵀ-natᵗ op f)
        ; delayᵀ-algebraicity      = λ τ → ≡ᵗ-≡ (delayᵀ-algebraicity τ)
        ; opᵀ-algebraicity         = λ op → ≡ᵗ-≡ (opᵀ-algebraicityᵗ op)
        ; strᵀ                     = strᵀ
        ; strᵀ-nat                 = λ f g → ≡ᵗ-≡ (strᵀ-nat f g)
        ; strᵀ-delayᵀ-algebraicity = ≡ᵗ-≡ strᵀ-delayᵀ-algebraicity
        ; T-alg-of-handlerᵀ        = T-alg-of-handlerᵀᵗ
        }

-- The model put together

TSetsModel : Model
TSetsModel = record
               { Cat = Cat
               ; Fut = Fut
               ; Pas = Pas
               ; Adj = Adj
               ; Typ = Typ
               ; Mon = Mon
               }
