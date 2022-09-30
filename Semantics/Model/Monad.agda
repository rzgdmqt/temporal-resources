------------------------------------------------------------
-- Strong graded monad equipped with algebraic operations --
------------------------------------------------------------

-- Note: A version of the monad that is not quotioned by
--       the delay equations (identity and composition)

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction
open import Semantics.Model.BaseGroundTypes

module Semantics.Model.Monad (Cat : Category)
                             (Fut : Future Cat)
                             (Pas : Past Cat)
                             (Adj : Adjunction Cat Fut Pas)
                             (Typ : BaseGroundTypes Cat Fut) where

open import Util.Equality
open import Util.Operations
open import Util.Time

open Category Cat
open Future Fut
open Past Pas
open Adjunction Adj
open BaseGroundTypes Typ

open import Semantics.Model.Category.Derived Cat
open import Semantics.Model.Modality.Past.Derived Cat Pas
open import Semantics.Model.Modality.Adjunction.Derived Cat Fut Pas Adj

record Monad : Set₁ where

  field

    -- MONAD STRUCTURE

    -- Functor
    
    Tᵒ : Obj → Time → Obj
    
    Tᶠ : ∀ {A B τ} → A →ᵐ B → Tᵒ A τ →ᵐ Tᵒ B τ

    -- Unit and multiplication

    ηᵀ : ∀ {A} → A →ᵐ Tᵒ A 0
    
    μᵀ : ∀ {A τ τ'} → Tᵒ (Tᵒ A τ') τ →ᵐ Tᵒ A (τ + τ')

    -- Equality coercion/substitutions

    τ-substᵀ : ∀ {A τ τ'} → τ ≡ τ' → Tᵒ A τ →ᵐ Tᵒ A τ'

    τ-substᵀ-refl : ∀ {A τ}
                  → τ-substᵀ {A} {τ} refl
                  ≡ idᵐ
    
    τ-substᵀ-trans : ∀ {A τ τ' τ''} → (p : τ ≡ τ') → (q : τ' ≡ τ'')
                   → τ-substᵀ q ∘ᵐ τ-substᵀ p
                   ≡ τ-substᵀ {A} (trans p q)

    -- Functoriality

    T-idᵐ : ∀ {A τ}
          → Tᶠ {A} {A} {τ} idᵐ
          ≡ idᵐ
    
    T-∘ᵐ : ∀ {A B C τ} → (g : B →ᵐ C) → (f : A →ᵐ B)
         → Tᶠ {A} {C} {τ} (g ∘ᵐ f)
         ≡ Tᶠ g ∘ᵐ Tᶠ f

    -- Unit and multiplication are natural

    ηᵀ-nat : ∀ {A B} → (f : A →ᵐ B) → ηᵀ ∘ᵐ f ≡ Tᶠ f ∘ᵐ ηᵀ
    
    μᵀ-nat : ∀ {A B τ τ'} → (f : A →ᵐ B)
           →    μᵀ {τ = τ} {τ' = τ'}
             ∘ᵐ Tᶠ (Tᶠ f)
           ≡    Tᶠ f
             ∘ᵐ μᵀ

    -- Graded monad laws

    T-μ∘η≡id : ∀ {A τ}
             →    μᵀ {τ = 0} {τ' = τ}
               ∘ᵐ ηᵀ {Tᵒ A τ}
             ≡ idᵐ
    
    T-μ∘Tη≡id : ∀ {A τ}
              →    μᵀ {τ = τ} {τ' = 0}
                ∘ᵐ Tᶠ (ηᵀ {A})
              ≡ τ-substᵀ (sym (+-identityʳ τ))
    
    T-μ∘μ≡μ∘Tμ : ∀ {A τ τ' τ''}
               →    μᵀ {A} {τ} {τ' + τ''}
                 ∘ᵐ Tᶠ μᵀ
               ≡    τ-substᵀ (+-assoc τ τ' τ'')
                 ∘ᵐ μᵀ
                 ∘ᵐ μᵀ

    -- EFFECTS

    -- Operations

    delayᵀ : ∀ {A} (τ : Time) {τ'} → [ τ ]ᵒ (Tᵒ A τ') →ᵐ Tᵒ A (τ + τ')
    
    opᵀ : ∀ {A τ} → (op : Op)
        → ⟦ param op ⟧ᵍ ×ᵐ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ A τ) →ᵐ Tᵒ A (op-time op + τ)

    -- Operations are natural

    delayᵀ-nat : ∀ {A B} (τ : Time) {τ'} → (f : A →ᵐ B)
               →    delayᵀ τ {τ' = τ'}
                 ∘ᵐ [ τ ]ᶠ (Tᶠ f)
               ≡    Tᶠ f
                 ∘ᵐ delayᵀ τ
               
    opᵀ-nat : ∀ {A B τ} → (op : Op) → (f : A →ᵐ B)
            →    opᵀ {τ = τ} op
              ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ f)))
            ≡    Tᶠ f
              ∘ᵐ opᵀ op

    -- Operations are algebraic

    delayᵀ-algebraicity : ∀ {A} (τ : Time) {τ' τ''}
                        →    μᵀ {A} {τ + τ'} {τ''}
                          ∘ᵐ delayᵀ τ {τ'}
                        ≡    τ-substᵀ (sym (+-assoc τ τ' τ''))
                          ∘ᵐ delayᵀ τ
                          ∘ᵐ [ τ ]ᶠ (μᵀ {A} {τ'} {τ''})
                        
    opᵀ-algebraicity : ∀ {A τ τ'} → (op : Op)
                     →    μᵀ {A} {op-time op + τ} {τ'}
                       ∘ᵐ opᵀ {τ = τ} op
                     ≡    τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
                       ∘ᵐ opᵀ op
                       ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ μᵀ))

    -- STRENGTH

    -- Strength

    strᵀ : ∀ {A B τ} → [ τ ]ᵒ A ×ᵐ Tᵒ B τ →ᵐ Tᵒ (A ×ᵐ B) τ

    -- Strength is natural
    
    strᵀ-nat : ∀ {A A' B B' τ} → (f : A →ᵐ A') → (g : B →ᵐ B')
             → strᵀ {A'} {B'} ∘ᵐ mapˣᵐ ([ τ ]ᶠ f) (Tᶠ g)
             ≡ Tᶠ (mapˣᵐ f g) ∘ᵐ strᵀ {A} {B}

    -- Strength laws

    strᵀ-ηᵀ : ∀ {A B}
            → strᵀ ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
            ≡ ηᵀ {A ×ᵐ B}

    strᵀ-μᵀ : ∀ {A B τ τ'}
            → μᵀ {A ×ᵐ B} {τ} {τ'} ∘ᵐ Tᶠ strᵀ ∘ᵐ strᵀ
            ≡ strᵀ ∘ᵐ mapˣᵐ δ⁻¹ μᵀ

    strᵀ-sndᵐ : ∀ {A B τ}
              → Tᶠ sndᵐ ∘ᵐ strᵀ {A} {B} {τ} ≡ sndᵐ

    strᵀ-assoc : ∀ {A B C τ}
               →    Tᶠ ×ᵐ-assoc
                 ∘ᵐ strᵀ
                 ∘ᵐ mapˣᵐ []-monoidal idᵐ ∘ᵐ ×ᵐ-assoc⁻¹
               ≡    strᵀ {A}
                 ∘ᵐ mapˣᵐ idᵐ (strᵀ {B} {C} {τ})

    -- Operations are algebraic wrt strength

    strᵀ-delayᵀ-algebraicity : ∀ {A B τ τ'}
                             →    strᵀ {A} {B} {τ + τ'}
                               ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ {τ'})
                             ≡    delayᵀ τ ∘ᵐ [ τ ]ᶠ (strᵀ {A} {B} {τ'})
                               ∘ᵐ []-monoidal ∘ᵐ mapˣᵐ (δ {A} {τ} {τ'}) idᵐ

    strᵀ-opᵀ-algebraicity : ∀ {A B τ} → (op : Op)
                          →    strᵀ {A} {B}
                            ∘ᵐ mapˣᵐ idᵐ (opᵀ op)
                          ≡    opᵀ op
                            ∘ᵐ mapˣᵐ
                                 idᵐ
                                 (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (strᵀ {A} {B} {τ})
                                                      ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                  ∘ᵐ []-monoidal
                                  ∘ᵐ mapˣᵐ (δ {A} {op-time op} {τ}) idᵐ)
                            ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ

    -- EFFECT HANDLING

    -- Turning an object of operation clauses to a T-algebra

    T-alg-of-handlerᵀ : ∀ {A τ τ'}
                      → Πᵐ Op (λ op → Πᵐ Time (λ τ'' →
                         ⟦ param op ⟧ᵍ ×ᵐ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ (Tᵒ A τ'')))
                           ⇒ᵐ Tᵒ A (op-time op + τ'')))
                      →ᵐ Tᵒ (Tᵒ A τ') τ ⇒ᵐ Tᵒ A (τ + τ')

    -- T-alg-of-handlerᵀ is an algebra

    T-alg-of-handlerᵀ-ηᵀ : ∀ {A τ}
                         →    uncurryᵐ T-alg-of-handlerᵀ
                           ∘ᵐ mapˣᵐ idᵐ (ηᵀ {Tᵒ A τ})
                         ≡ sndᵐ

    T-alg-of-handlerᵀ-delayᵀ : ∀ {A τ τ' τ''}
                             →    uncurryᵐ T-alg-of-handlerᵀ
                               ∘ᵐ mapˣᵐ idᵐ (delayᵀ {Tᵒ A τ''} τ {τ'})
                             ≡    τ-substᵀ (sym (+-assoc τ τ' τ''))
                               ∘ᵐ delayᵀ τ
                               ∘ᵐ [ τ ]ᶠ (uncurryᵐ T-alg-of-handlerᵀ)
                               ∘ᵐ [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
                               ∘ᵐ []-monoidal
                               ∘ᵐ mapˣᵐ η⊣ idᵐ

    T-alg-of-handlerᵀ-opᵀ : ∀ {A τ τ'} → (op : Op)
                          →    uncurryᵐ T-alg-of-handlerᵀ
                            ∘ᵐ mapˣᵐ idᵐ (opᵀ {Tᵒ A τ'} {τ} op)
                          ≡    τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
                            ∘ᵐ appᵐ
                            ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
                            ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))))
                            ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
                            ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
                            ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ (η⊣ {τ = op-time op}) idᵐ))
                            ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                            ∘ᵐ mapˣᵐ (projᵐ (τ + τ') ∘ᵐ projᵐ op) idᵐ
                            ∘ᵐ ⟨ fstᵐ , idᵐ ⟩ᵐ

    -- ...
