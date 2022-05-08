-------------------------------------------------------------
-- Interpretation of well-typed terms in time-varying sets --
-------------------------------------------------------------

open import Function

open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Semantics.TSets
open import Semantics.Monad

open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Modality.Adjunction

open import Util.Equality
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

⟦⟧ᵛ-⟦⟧ᵍ : (B : GType) → ⟦ type-of-gtype B ⟧ᵛ →ᵗ ⟦ B ⟧ᵍ
⟦⟧ᵛ-⟦⟧ᵍ (Base B) = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ Unit     = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ Empty    = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A)

⟦⟧ᵍ-⟦⟧ᵛ : (B : GType) → ⟦ B ⟧ᵍ →ᵗ ⟦ type-of-gtype B ⟧ᵛ
⟦⟧ᵍ-⟦⟧ᵛ (Base B) = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ Unit     = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ Empty    = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A)

-- Interpretation of contexts as functors

⟦_⟧ᵉᵒ : Ctx → TSet → TSet
⟦ [] ⟧ᵉᵒ      B = B
⟦ Γ ∷ A ⟧ᵉᵒ   B = ⟦ Γ ⟧ᵉᵒ B ×ᵗ ⟦ A ⟧ᵛ
⟦ Γ ⟨ τ ⟩ ⟧ᵉᵒ B = ⟨ τ ⟩ᵒ (⟦ Γ ⟧ᵉᵒ B)

⟦_⟧ᵉᶠ : ∀ {A B} → (Γ : Ctx) → A →ᵗ B → ⟦ Γ ⟧ᵉᵒ A →ᵗ ⟦ Γ ⟧ᵉᵒ B
⟦ [] ⟧ᵉᶠ      f = f
⟦ Γ ∷ A ⟧ᵉᶠ   f = mapˣᵗ (⟦ Γ ⟧ᵉᶠ f) idᵗ
⟦ Γ ⟨ τ ⟩ ⟧ᵉᶠ f = ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)

-- Environments are such functors applied to the terminal object

⟦_⟧ᵉ : Ctx → TSet
⟦ Γ ⟧ᵉ = ⟦ Γ ⟧ᵉᵒ 𝟙ᵗ

infix 25 ⟦_⟧ᵉ

-- Splitting an environment according to context splitting

split-env : ∀ {Γ Γ' Γ''}
          → Γ' , Γ'' split Γ
          → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵗ ⟦ Γ'' ⟧ᵉᵒ (⟦ Γ' ⟧ᵉᵒ A)
          
split-env split-[]             = idᵗ
split-env (split-∷ p)          = mapˣᵗ (split-env p) idᵗ
split-env (split-⟨⟩ {τ = τ} p) = ⟨ τ ⟩ᶠ (split-env p)

-- Total time-passage of an environment as a single ⟨_⟩ modality

env-ctx-time-⟨⟩ : (Γ : Ctx)
                → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵗ ⟨ ctx-time Γ ⟩ᵒ A

env-ctx-time-⟨⟩ []        = η
env-ctx-time-⟨⟩ (Γ ∷ A)   = env-ctx-time-⟨⟩ Γ ∘ᵗ fstᵗ
env-ctx-time-⟨⟩ (Γ ⟨ τ ⟩) {A} =
     ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
  ∘ᵗ μ {A}
  ∘ᵗ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)

-- Interaction of ⟨_⟩ modality and the time-travelling operation on contexts

env-⟨⟩-ᶜ : ∀ {Γ}
         → (τ : Time) → τ ≤ ctx-time Γ
         → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵗ ⟨ τ ⟩ᵒ (⟦ Γ -ᶜ τ ⟧ᵉᵒ A)
         
env-⟨⟩-ᶜ {Γ} zero p =
  η
env-⟨⟩-ᶜ {Γ ∷ B} (suc τ) p =
     env-⟨⟩-ᶜ {Γ} (suc τ) p
  ∘ᵗ fstᵗ
env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} (suc τ) p {A} with suc τ ≤? τ'
... | yes q =
     μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} {suc τ} {τ' ∸ suc τ}
  ∘ᵗ ⟨⟩-≤ {⟦ Γ ⟧ᵉᵒ A} (≤-reflexive (m+[n∸m]≡n q))
... | no ¬q =
     ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} (m≤n+m∸n (suc τ) τ')
  ∘ᵗ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉᵒ A} {τ'} {suc τ ∸ τ'}
  ∘ᵗ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
       (≤-trans
         (∸-monoˡ-≤ τ' p)
         (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))

-- Projecting a variable out of an environment

var-in-env : ∀ {Γ A τ} → (x : A ∈[ τ ] Γ) → ⟦ Γ ⟧ᵉ →ᵗ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᵒ ⟦ A ⟧ᵛ
var-in-env Hd        = sndᵗ
var-in-env (Tl-∷ x)  = mapˣᵗ (var-in-env x) idᵗ
var-in-env (Tl-⟨⟩ {τ = τ} x) = ⟨ τ ⟩ᶠ (var-in-env x)

-- Semantic constants for base-typed value constants

constᵗ : ∀ {B} → BaseSet B → 𝟙ᵗ →ᵗ ConstTSet (BaseSet B)
constᵗ c = tset-map (λ _ → c) (λ _ _ → refl)

-- Interpretation of well-typed value and computation terms

mutual

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → Γ ⊢V⦂ A → ⟦ Γ ⟧ᵉ →ᵗ ⟦ A ⟧ᵛ
  
  ⟦ var x ⟧ᵛᵗ =
       ε-⟨⟩
    ∘ᵗ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵗ var-in-env x
  
  ⟦ const c ⟧ᵛᵗ = constᵗ c ∘ᵗ terminalᵗ
  
  ⟦ ⋆ ⟧ᵛᵗ = terminalᵗ
  
  ⟦ lam M ⟧ᵛᵗ = curryᵗ ⟦ M ⟧ᶜᵗ
  
  ⟦ box {τ = τ} V ⟧ᵛᵗ = [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ η-⊣ 

  infix 25 ⟦_⟧ᵛᵗ


  ⟦_⟧ᶜᵗ : ∀ {Γ C} → Γ ⊢C⦂ C → ⟦ Γ ⟧ᵉ →ᵗ ⟦ C ⟧ᶜ
  
  ⟦ return V ⟧ᶜᵗ = ηᵀ ∘ᵗ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (_;_ {τ = τ} M N) =
       μᵀ
    ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} 
    ∘ᵗ ⟨ η-⊣ {⟦ Γ ⟧ᵉ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ

  ⟦ V · W ⟧ᶜᵗ = appᵗ ∘ᵗ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵗ
  
  ⟦ absurd V ⟧ᶜᵗ = initialᵗ ∘ᵗ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {τ} op V M) =
    let f : ⟦ Γ ⟧ᵉ →ᵗ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵗ Tᵒ ⟦ A ⟧ᵛ τ)
        f = [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ) ∘ᵗ η-⊣ in
    let g : [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵗ Tᵒ ⟦ A ⟧ᵛ τ)
         →ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ ⟦ A ⟧ᵛ τ)
        g = [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) (idᵗ {Tᵒ ⟦ A ⟧ᵛ τ})) in
    opᵀ op ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ,
                g ∘ᵗ f ⟩ᵗ

  ⟦_⟧ᶜᵗ {Γ} (handle_`with_`in {A} {B} {τ} {τ'} M H N) =
    let f : ⟦ Γ ⟧ᵉ →ᵗ Π Op (λ op → Π Time (λ τ'' → ⟦ Γ ⟧ᵉ))
        f = ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ in
    let g : (op : Op) → (τ'' : Time)
          → ⟦ type-of-gtype (param op) ⟧ᵛ ×ᵗ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ
              ⇒ᵗ (Tᵒ ⟦ B ⟧ᵛ τ'')) ⇒ᵗ Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')
          →ᵗ ⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ
              ⇒ᵗ (Tᵒ ⟦ B ⟧ᵛ τ'')) ⇒ᵗ Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')
        g = λ op τ'' →
               map⇒ᵗ
                 (mapˣᵗ
                   (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                   ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) (idᵗ {Tᵒ ⟦ B ⟧ᵛ τ''}))))
                 (idᵗ {Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')}) in
       uncurryᵗ (
            alg-of-handler
         ∘ᵗ mapⁱˣᵗ (λ op → mapⁱˣᵗ (λ τ'' →
              g op τ'' ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×-assocᵗ)))
         ∘ᵗ f)
    ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵗ mapˣᵗ idᵗ (strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ})
    ∘ᵗ ⟨ idᵗ , ⟨ η-⊣ {⟦ Γ ⟧ᵉ} {τ = τ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ ⟩ᵗ

  ⟦ unbox {τ = τ} p V M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵗ ⟨ idᵗ ,
                    ε-⊣ {τ = τ}
                 ∘ᵗ (⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ)
                 ∘ᵗ env-⟨⟩-ᶜ τ p ⟩ᵗ

  ⟦ delay τ refl M ⟧ᶜᵗ =
       T-≤τ (≤-reflexive (+-comm τ _))
    ∘ᵗ T-delay ∘ᵗ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ)
    ∘ᵗ η-⊣ 
    
  infix 25 ⟦_⟧ᶜᵗ

