-----------------------------------------------------------------------------
-- Strong (via enrichment) graded monad equipped with algebraic operations --
-----------------------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction
open import Semantics.Model.BaseGroundTypes

module Semantics.Model.Monad.Enriched (Cat : Category)
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
open import Semantics.Model.Modality.Future.Derived Cat Fut
open import Semantics.Model.Modality.Past.Derived Cat Pas
open import Semantics.Model.Modality.Adjunction.Derived Cat Fut Pas Adj

record EMonad : Set₁ where

  field

    -- MONAD STRUCTURE

    -- Functor
    
    ETᵒ : Obj → Time → Obj
    
    ETᶠ : ∀ {A B τ} → A →ᵐ B → ETᵒ A τ →ᵐ ETᵒ B τ

    -- Unit and multiplication

    ηᴱᵀ : ∀ {A} → A →ᵐ ETᵒ A 0
    
    μᴱᵀ : ∀ {A τ τ'} → ETᵒ (ETᵒ A τ') τ →ᵐ ETᵒ A (τ + τ')

    -- Equality coercion/substitutions

    τ-substᴱᵀ : ∀ {A τ τ'} → τ ≡ τ' → ETᵒ A τ →ᵐ ETᵒ A τ'

    τ-substᴱᵀ-refl : ∀ {A τ}
                   → τ-substᴱᵀ {A} {τ} refl
                   ≡ idᵐ
    
    τ-substᴱᵀ-trans : ∀ {A τ τ' τ''} → (p : τ ≡ τ') → (q : τ' ≡ τ'')
                    → τ-substᴱᵀ q ∘ᵐ τ-substᴱᵀ p
                    ≡ τ-substᴱᵀ {A} (trans p q)

    -- Functoriality

    ET-idᵐ : ∀ {A τ}
           → ETᶠ {A} {A} {τ} idᵐ
           ≡ idᵐ
    
    ET-∘ᵐ : ∀ {A B C τ} → (g : B →ᵐ C) → (f : A →ᵐ B)
          → ETᶠ {A} {C} {τ} (g ∘ᵐ f)
          ≡ ETᶠ g ∘ᵐ ETᶠ f

    -- Unit and multiplication are natural

    ηᴱᵀ-nat : ∀ {A B} → (f : A →ᵐ B) → ηᴱᵀ ∘ᵐ f ≡ ETᶠ f ∘ᵐ ηᴱᵀ
    
    μᴱᵀ-nat : ∀ {A B τ τ'} → (f : A →ᵐ B)
            →    μᴱᵀ {τ = τ} {τ' = τ'}
              ∘ᵐ ETᶠ (ETᶠ f)
            ≡    ETᶠ f
              ∘ᵐ μᴱᵀ

    -- Graded monad laws

    ET-μ∘η≡id : ∀ {A τ}
              →    μᴱᵀ {τ = 0} {τ' = τ}
                ∘ᵐ ηᴱᵀ {ETᵒ A τ}
              ≡ idᵐ
    
    ET-μ∘ETη≡id : ∀ {A τ}
                →    μᴱᵀ {τ = τ} {τ' = 0}
                  ∘ᵐ ETᶠ (ηᴱᵀ {A})
                ≡ τ-substᴱᵀ (sym (+-identityʳ τ))
    
    ET-μ∘μ≡μ∘ETμ : ∀ {A τ τ' τ''}
                 →    μᴱᵀ {A} {τ} {τ' + τ''}
                   ∘ᵐ ETᶠ μᴱᵀ
                 ≡    τ-substᴱᵀ (+-assoc τ τ' τ'')
                   ∘ᵐ μᴱᵀ
                   ∘ᵐ μᴱᵀ

    -- EFFECTS

    -- Operations

    delayᴱᵀ : ∀ {A} (τ : Time) {τ'} → [ τ ]ᵒ (ETᵒ A τ') →ᵐ ETᵒ A (τ + τ')
    
    opᴱᵀ : ∀ {A τ} → (op : Op)
         → ⟦ param op ⟧ᵍ ×ᵐ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ ETᵒ A τ) →ᵐ ETᵒ A (op-time op + τ)

    -- Operations are natural

    delayᴱᵀ-nat : ∀ {A B} (τ : Time) {τ'} → (f : A →ᵐ B)
                →    delayᴱᵀ τ {τ' = τ'}
                  ∘ᵐ [ τ ]ᶠ (ETᶠ f)
                ≡    ETᶠ f
                  ∘ᵐ delayᴱᵀ τ
               
    opᴱᵀ-nat : ∀ {A B τ} → (op : Op) → (f : A →ᵐ B)
             →    opᴱᵀ {τ = τ} op
               ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (ETᶠ f)))
             ≡    ETᶠ f
               ∘ᵐ opᴱᵀ op

    -- Operations are algebraic

    delayᴱᵀ-algebraicity : ∀ {A} (τ : Time) {τ' τ''}
                         →    μᴱᵀ {A} {τ + τ'} {τ''}
                           ∘ᵐ delayᴱᵀ τ {τ'}
                         ≡    τ-substᴱᵀ (sym (+-assoc τ τ' τ''))
                           ∘ᵐ delayᴱᵀ τ
                           ∘ᵐ [ τ ]ᶠ (μᴱᵀ {A} {τ'} {τ''})
                        
    opᴱᵀ-algebraicity : ∀ {A τ τ'} → (op : Op)
                      →    μᴱᵀ {A} {op-time op + τ} {τ'}
                        ∘ᵐ opᴱᵀ {τ = τ} op
                      ≡    τ-substᴱᵀ (sym (+-assoc (op-time op) τ τ'))
                        ∘ᵐ opᴱᵀ op
                        ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ μᴱᵀ))

    -- [-]-ENRICHMENT

    -- Modal enrichment

    enrᴱᵀ : ∀ {A B τ} → [ τ ]ᵒ (A ⇒ᵐ B) →ᵐ ETᵒ A τ ⇒ᵐ ETᵒ B τ

    -- Enrichment is natural

    enrᴱᵀ-nat : ∀ {A B C D τ}
              → (f : A →ᵐ B)
              → (g : C →ᵐ D)
              →    map⇒ᵐ (ETᶠ f) (ETᶠ g)
                ∘ᵐ enrᴱᵀ {B} {C} {τ}
              ≡    enrᴱᵀ
                ∘ᵐ [ τ ]ᶠ (map⇒ᵐ f g)

    -- Enrichment laws

    enrᴱᵀ-ηᴱᵀ : ∀ {A B}
              →    uncurryᵐ enrᴱᵀ
                ∘ᵐ mapˣᵐ ε⁻¹ ηᴱᵀ
              ≡    ηᴱᵀ
                ∘ᵐ appᵐ {A} {B}

    enrᴱᵀ-μᴱᵀ : ∀ {A B τ τ'}
              →    μᴱᵀ {B} {τ} {τ'}
                ∘ᵐ ETᶠ (uncurryᵐ (enrᴱᵀ {A} {B} {τ'} ))
                ∘ᵐ uncurryᵐ enrᴱᵀ
                ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
              ≡    uncurryᵐ enrᴱᵀ
                ∘ᵐ mapˣᵐ δ⁻¹ (μᴱᵀ {A} {τ} {τ'})

    enrᴱᵀ-idᵐ : ∀ {A τ}
              →    uncurryᵐ (enrᴱᵀ {A} {A} {τ})
                ∘ᵐ mapˣᵐ η-[] idᵐ
                ∘ᵐ mapˣᵐ {𝟙ᵐ} (curryᵐ sndᵐ) idᵐ
              ≡ sndᵐ

    enrᴱᵀ-idᵐ-∘ᵐ : ∀ {A B C τ}
                 →    uncurryᵐ (enrᴱᵀ {B} {C} {τ})
                   ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ (enrᴱᵀ {A} {B} {τ}))
                 ≡    uncurryᵐ (enrᴱᵀ {A} {C} {τ})
                   ∘ᵐ mapˣᵐ
                       ([ τ ]ᶠ (curryᵐ (   appᵐ
                                        ∘ᵐ mapˣᵐ idᵐ appᵐ
                                        ∘ᵐ ×ᵐ-assoc)))
                       idᵐ
                   ∘ᵐ mapˣᵐ []-monoidal idᵐ
                   ∘ᵐ ×ᵐ-assoc⁻¹

    -- Operations are algebraic wrt enrichment

    enrᴱᵀ-delayᴱᵀ-algebraicity : ∀ {A B τ τ'}
                               →    uncurryᵐ (enrᴱᵀ {A} {B} {τ + τ'})
                                 ∘ᵐ mapˣᵐ idᵐ (delayᴱᵀ τ {τ'})
                               ≡    delayᴱᵀ τ
                                 ∘ᵐ [ τ ]ᶠ (uncurryᵐ (enrᴱᵀ {A} {B} {τ'}))
                                 ∘ᵐ []-monoidal
                                 ∘ᵐ mapˣᵐ (δ {A ⇒ᵐ B} {τ} {τ'}) idᵐ

    enrᴱᵀ-opᴱᵀ-algebraicity : ∀ {A B τ} → (op : Op)
                            →    uncurryᵐ (enrᴱᵀ {A} {B})
                              ∘ᵐ mapˣᵐ idᵐ (opᴱᵀ op)
                            ≡    opᴱᵀ op
                              ∘ᵐ mapˣᵐ
                                   idᵐ
                                   (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {A} {B} {τ}))
                                                        ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                    ∘ᵐ []-monoidal
                                    ∘ᵐ mapˣᵐ δ idᵐ)
                              ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    

    -- EFFECT HANDLING

    -- Turning an object of operation clauses to a T-algebra

    ET-alg-of-handlerᴱᵀ : ∀ {A τ τ'}
                        → Πᵐ Op (λ op → Πᵐ Time (λ τ'' →
                           ⟦ param op ⟧ᵍ ×ᵐ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ (ETᵒ A τ'')))
                             ⇒ᵐ ETᵒ A (op-time op + τ'')))
                        →ᵐ ETᵒ (ETᵒ A τ') τ ⇒ᵐ ETᵒ A (τ + τ')

    -- T-alg-of-handlerᴱᵀ is an algebra for the operations

    ET-alg-of-handlerᴱᵀ-ηᴱᵀ : ∀ {A τ}
                            →    uncurryᵐ ET-alg-of-handlerᴱᵀ
                              ∘ᵐ mapˣᵐ idᵐ (ηᴱᵀ {ETᵒ A τ})
                            ≡ sndᵐ

    ET-alg-of-handlerᴱᵀ-delayᴱᵀ : ∀ {A τ τ' τ''}
                                →    uncurryᵐ ET-alg-of-handlerᴱᵀ
                                  ∘ᵐ mapˣᵐ idᵐ (delayᴱᵀ {ETᵒ A τ''} τ {τ'})
                                ≡    τ-substᴱᵀ (sym (+-assoc τ τ' τ''))
                                  ∘ᵐ delayᴱᵀ τ
                                  ∘ᵐ [ τ ]ᶠ (uncurryᵐ (ET-alg-of-handlerᴱᵀ {τ = τ'} {τ' = τ''}))
                                  ∘ᵐ [ τ ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)
                                  ∘ᵐ []-monoidal
                                  ∘ᵐ mapˣᵐ η⊣ idᵐ

    ET-alg-of-handlerᴱᵀ-opᴱᵀ : ∀ {A τ τ'} → (op : Op)
                             →    uncurryᵐ ET-alg-of-handlerᴱᵀ
                               ∘ᵐ mapˣᵐ idᵐ (opᴱᵀ {ETᵒ A τ'} {τ} op)
                             ≡    τ-substᴱᵀ (sym (+-assoc (op-time op) τ τ'))
                               ∘ᵐ appᵐ
                               ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ ET-alg-of-handlerᴱᵀ))))
                               ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))))
                               ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
                               ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
                               ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ (η⊣ {τ = op-time op}) idᵐ))
                               ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                               ∘ᵐ mapˣᵐ (projᵐ (τ + τ') ∘ᵐ projᵐ op) idᵐ
                               ∘ᵐ ⟨ fstᵐ , idᵐ ⟩ᵐ
