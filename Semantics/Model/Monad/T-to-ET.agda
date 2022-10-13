-----------------------------------------------------------------------------
-- Strong (via enrichment) graded monad equipped with algebraic operations --
-----------------------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction
open import Semantics.Model.BaseGroundTypes

module Semantics.Model.Monad.T-to-ET (Cat : Category)
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

open import Semantics.Model.Monad Cat Fut Pas Adj Typ

open import Semantics.Model.Monad.Enriched Cat Fut Pas Adj Typ

-- Showing that [-]-enrichment follows from [-]-strength

T-to-ET : Monad → EMonad
T-to-ET M = record
              { ETᵒ = Tᵒ
              ; ETᶠ = Tᶠ
              ; ηᴱᵀ = ηᵀ
              ; μᴱᵀ = μᵀ
              ; τ-substᴱᵀ = τ-substᵀ
              ; τ-substᴱᵀ-refl = τ-substᵀ-refl
              ; τ-substᴱᵀ-trans = τ-substᵀ-trans
              ; ET-idᵐ = T-idᵐ
              ; ET-∘ᵐ = T-∘ᵐ
              ; ηᴱᵀ-nat = ηᵀ-nat
              ; μᴱᵀ-nat = μᵀ-nat
              ; ET-μ∘η≡id = T-μ∘η≡id
              ; ET-μ∘ETη≡id = T-μ∘Tη≡id
              ; ET-μ∘μ≡μ∘ETμ = T-μ∘μ≡μ∘Tμ
              ; delayᴱᵀ = delayᵀ
              ; opᴱᵀ = opᵀ
              ; delayᴱᵀ-nat = delayᵀ-nat
              ; opᴱᵀ-nat = opᵀ-nat
              ; delayᴱᵀ-algebraicity = delayᵀ-algebraicity
              ; opᴱᵀ-algebraicity = opᵀ-algebraicity
              ; enrᴱᵀ = enrᴱᵀ
              ; enrᴱᵀ-nat = enrᴱᵀ-nat
              ; enrᴱᵀ-ηᴱᵀ = enrᴱᵀ-ηᴱᵀ
              ; enrᴱᵀ-μᴱᵀ = enrᴱᵀ-μᴱᵀ
              ; enrᴱᵀ-idᵐ = enrᴱᵀ-idᵐ
              ; enrᴱᵀ-idᵐ-∘ᵐ = enrᴱᵀ-∘ᵐ
              ; enrᴱᵀ-delayᴱᵀ-algebraicity = enrᴱᵀ-delayᴱᵀ-algebraicity
              ; enrᴱᵀ-opᴱᵀ-algebraicity = enrᴱᵀ-opᴱᵀ-algebraicity
              ; ET-alg-of-handlerᴱᵀ = T-alg-of-handlerᵀ
              ; ET-alg-of-handlerᴱᵀ-ηᴱᵀ = T-alg-of-handlerᵀ-ηᵀ
              ; ET-alg-of-handlerᴱᵀ-delayᴱᵀ = T-alg-of-handlerᵀ-delayᵀ
              ; ET-alg-of-handlerᴱᵀ-opᴱᵀ = T-alg-of-handlerᵀ-opᵀ
              }

  where

    open Monad M

    enrᴱᵀ : ∀ {A B τ} → [ τ ]ᵒ (A ⇒ᵐ B) →ᵐ Tᵒ A τ ⇒ᵐ Tᵒ B τ
    enrᴱᵀ {A} {B} {τ} =
      curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
              ∘ᵐ strᵀ)

    enrᴱᵀ-nat : ∀ {A B C D τ}
              → (f : A →ᵐ B)
              → (g : C →ᵐ D)
              → map⇒ᵐ (Tᶠ f) (Tᶠ g) ∘ᵐ enrᴱᵀ
              ≡ enrᴱᵀ ∘ᵐ [ τ ]ᶠ (map⇒ᵐ f g)

    enrᴱᵀ-nat {A} {B} {C} {D} {τ} f g =
      begin
           map⇒ᵐ (Tᶠ f) (Tᶠ g)
        ∘ᵐ enrᴱᵀ
      ≡⟨⟩
           map⇒ᵐ (Tᶠ f) (Tᶠ g)
        ∘ᵐ curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                   ∘ᵐ strᵀ)
      ≡⟨⟩
           curryᵐ (Tᶠ g ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
        ∘ᵐ curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
      ≡⟨ trans (sym (curryᵐ-nat _ _)) (cong curryᵐ
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ uncurryᵐ idᵐ
                ∘ᵐ mapˣᵐ idᵐ (Tᶠ f)
                ∘ᵐ mapˣᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)) idᵐ)
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ
              (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
              (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))))))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ uncurryᵐ idᵐ
                ∘ᵐ mapˣᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)) idᵐ
                ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _))))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
                ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-identityˡ _)))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
                ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ Tᶠ (uncurryᵐ idᵐ)
                ∘ᵐ strᵀ
                ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ mapˣᵐ (sym []-idᵐ) refl)))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ Tᶠ (uncurryᵐ idᵐ)
                ∘ᵐ strᵀ
                ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) (Tᶠ f))
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (strᵀ-nat _ _))) ⟩
        curryᵐ (   Tᶠ g
                ∘ᵐ Tᶠ (uncurryᵐ idᵐ)
                ∘ᵐ Tᶠ (mapˣᵐ idᵐ f)
                ∘ᵐ strᵀ)
      ≡⟨ cong curryᵐ (sym
          (trans (∘ᵐ-congˡ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
        curryᵐ (   Tᶠ (g ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ f)
                ∘ᵐ strᵀ)
      ≡⟨ cong curryᵐ (∘ᵐ-congˡ (cong Tᶠ (sym (curryᵐ-uncurryᵐ-iso _)))) ⟩
        curryᵐ (   Tᶠ (uncurryᵐ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)))
                ∘ᵐ strᵀ)
      ≡⟨ cong curryᵐ (∘ᵐ-congˡ (cong Tᶠ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _))))) ⟩
        curryᵐ (   Tᶠ (uncurryᵐ (idᵐ ∘ᵐ curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)))
                ∘ᵐ strᵀ)
      ≡⟨ cong curryᵐ (∘ᵐ-congˡ (cong Tᶠ (uncurryᵐ-nat _ _))) ⟩
        curryᵐ (   Tᶠ (   uncurryᵐ idᵐ
                       ∘ᵐ mapˣᵐ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)) idᵐ)
                ∘ᵐ strᵀ)
      ≡⟨ cong curryᵐ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (T-∘ᵐ _ _))))) ⟩
        curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                ∘ᵐ Tᶠ (mapˣᵐ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)) idᵐ)
                ∘ᵐ strᵀ)
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (strᵀ-nat _ _))) ⟩
        curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                ∘ᵐ strᵀ
                ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f))) (Tᶠ idᵐ))
      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ mapˣᵐ refl T-idᵐ))) ⟩
        curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                ∘ᵐ strᵀ
                ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f))) idᵐ)
      ≡⟨ trans (cong curryᵐ (sym (∘ᵐ-assoc _ _ _))) (curryᵐ-nat _ _) ⟩
           curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                   ∘ᵐ strᵀ)
        ∘ᵐ [ τ ]ᶠ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f))
      ≡⟨⟩
           curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                   ∘ᵐ strᵀ)
        ∘ᵐ [ τ ]ᶠ (map⇒ᵐ f g)
      ≡⟨⟩
           enrᴱᵀ
        ∘ᵐ [ τ ]ᶠ (map⇒ᵐ f g)
      ∎

    enrᴱᵀ-ηᴱᵀ : ∀ {A B}
              → uncurryᵐ (enrᴱᵀ {A} {B}) ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
              ≡ ηᵀ ∘ᵐ appᵐ

    enrᴱᵀ-ηᴱᵀ {A} {B} = 
      begin
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
      ≡⟨⟩
           uncurryᵐ (curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
                             ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
      ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ε⁻¹ ηᵀ
      ≡⟨ ∘ᵐ-congʳ strᵀ-ηᵀ ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ ηᵀ
      ≡⟨ sym (ηᵀ-nat _) ⟩
           ηᵀ
        ∘ᵐ uncurryᵐ idᵐ
      ∎

    enrᴱᵀ-μᴱᵀ : ∀ {A B τ τ'}
              →    μᵀ {B} {τ} {τ'}
                ∘ᵐ Tᶠ (uncurryᵐ (enrᴱᵀ {A} {B} {τ'}))
                ∘ᵐ uncurryᵐ enrᴱᵀ ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
              ≡    uncurryᵐ enrᴱᵀ
                ∘ᵐ mapˣᵐ δ⁻¹ μᵀ

    enrᴱᵀ-μᴱᵀ {A} {B} {τ} {τ'} =
      begin
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (uncurryᵐ (enrᴱᵀ {A} {B} {τ'}))
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)))
        ∘ᵐ uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (curryᵐ-uncurryᵐ-iso _))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (sym T-idᵐ))))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) (Tᶠ idᵐ)
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (strᵀ-nat _ _))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ (curryᵐ idᵐ) idᵐ)
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (T-∘ᵐ _ _))))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ (   uncurryᵐ idᵐ
               ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ)
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (sym (uncurryᵐ-nat _ _))))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ (uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ))
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (cong uncurryᵐ (∘ᵐ-identityˡ _))))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ (uncurryᵐ (curryᵐ idᵐ))
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (curryᵐ-uncurryᵐ-iso _)))) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ Tᶠ idᵐ
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ T-idᵐ)) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ idᵐ
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) ⟩
           μᵀ {B} {τ} {τ'}
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)) ⟩
           μᵀ
        ∘ᵐ Tᶠ (Tᶠ (uncurryᵐ idᵐ))
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (μᵀ-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ μᵀ
        ∘ᵐ Tᶠ strᵀ
        ∘ᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ strᵀ-μᵀ ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ δ⁻¹ μᵀ
      ≡⟨ sym (trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _)) ⟩
           uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ δ⁻¹ μᵀ
      ≡⟨⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ δ⁻¹ μᵀ
      ∎

    enrᴱᵀ-idᵐ : ∀ {A τ}
              →    uncurryᵐ (enrᴱᵀ {A} {A} {τ})
                ∘ᵐ mapˣᵐ η-[] idᵐ
                ∘ᵐ mapˣᵐ {𝟙ᵐ} (curryᵐ sndᵐ) idᵐ
              ≡ sndᵐ

    enrᴱᵀ-idᵐ {A} {τ} =
      begin
           uncurryᵐ (enrᴱᵀ {A} {A} {τ})
        ∘ᵐ mapˣᵐ η-[] idᵐ
        ∘ᵐ mapˣᵐ {𝟙ᵐ} (curryᵐ sndᵐ) idᵐ
      ≡⟨⟩
           uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ η-[] idᵐ
        ∘ᵐ mapˣᵐ {𝟙ᵐ} (curryᵐ sndᵐ) idᵐ
      ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η-[] idᵐ
        ∘ᵐ mapˣᵐ {𝟙ᵐ} (curryᵐ sndᵐ) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym
          (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ
              (η-[]-nat _)
              (∘ᵐ-congˡ T-idᵐ)))))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ sndᵐ)) (Tᶠ idᵐ)
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ (curryᵐ sndᵐ) idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (T-∘ᵐ _ _))) ⟩
           Tᶠ (   uncurryᵐ idᵐ
               ∘ᵐ mapˣᵐ (curryᵐ sndᵐ) idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (sym (uncurryᵐ-nat _ _))) ⟩
           Tᶠ (uncurryᵐ (idᵐ ∘ᵐ curryᵐ sndᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (cong uncurryᵐ (∘ᵐ-identityˡ _))) ⟩
           Tᶠ (uncurryᵐ (curryᵐ sndᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (curryᵐ-uncurryᵐ-iso _)) ⟩
           Tᶠ sndᵐ
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
          (   Tᶠ sndᵐ
           ∘ᵐ strᵀ)
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ ∘ᵐ-congˡ strᵀ-sndᵐ ⟩
           sndᵐ
        ∘ᵐ mapˣᵐ η-[] idᵐ
      ≡⟨ trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _) ⟩
        sndᵐ
      ∎

    enrᴱᵀ-∘ᵐ : ∀ {A B C τ}
             →    uncurryᵐ (enrᴱᵀ {B} {C} {τ})
               ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ (enrᴱᵀ {A} {B} {τ}))
             ≡    uncurryᵐ (enrᴱᵀ {A} {C} {τ})
               ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))) idᵐ
               ∘ᵐ mapˣᵐ []-monoidal idᵐ
               ∘ᵐ ×ᵐ-assoc⁻¹

    enrᴱᵀ-∘ᵐ {A} {B} {C} {τ} =
      begin
           uncurryᵐ (enrᴱᵀ {B} {C} {τ})
        ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ (enrᴱᵀ {A} {B} {τ}))
      ≡⟨⟩
           uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)))
      ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (curryᵐ-uncurryᵐ-iso _))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans
          (cong₂ mapˣᵐ
            (sym (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _)))
            refl)
          (mapˣᵐ-∘ᵐ _ _ _ _))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ idᵐ) (Tᶠ (uncurryᵐ idᵐ))
        ∘ᵐ mapˣᵐ idᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (strᵀ-nat _ _)) (∘ᵐ-assoc _ _ _))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ (uncurryᵐ idᵐ))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ strᵀ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym strᵀ-assoc)) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ idᵐ (uncurryᵐ idᵐ))
        ∘ᵐ Tᶠ ×ᵐ-assoc
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ sym (trans (∘ᵐ-congˡ (trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
           Tᶠ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ) ∘ᵐ ×ᵐ-assoc)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (sym (curryᵐ-uncurryᵐ-iso _))) ⟩
           Tᶠ (uncurryᵐ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc)))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _)))) ⟩
           Tᶠ (uncurryᵐ (idᵐ ∘ᵐ curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc)))
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong Tᶠ (uncurryᵐ-nat _ _)) ⟩
           Tᶠ (   uncurryᵐ idᵐ
               ∘ᵐ mapˣᵐ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc)) idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ Tᶠ (mapˣᵐ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc)) idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (sym (strᵀ-nat _ _))) (∘ᵐ-assoc _ _ _))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))) (Tᶠ idᵐ)
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl T-idᵐ))) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (curryᵐ-uncurryᵐ-iso _))) ⟩
           uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨⟩
           uncurryᵐ (enrᴱᵀ {A} {C} {τ})
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ appᵐ ∘ᵐ ×ᵐ-assoc))) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ∎

    enrᴱᵀ-delayᴱᵀ-algebraicity : ∀ {A B τ τ'}
                               →    uncurryᵐ (enrᴱᵀ {A} {B} {τ + τ'})
                                 ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ {τ'})
                               ≡    delayᵀ τ
                                 ∘ᵐ [ τ ]ᶠ (uncurryᵐ (enrᴱᵀ {A} {B} {τ'}))
                                 ∘ᵐ []-monoidal
                                 ∘ᵐ mapˣᵐ (δ {A ⇒ᵐ B} {τ} {τ'}) idᵐ
                                 
    enrᴱᵀ-delayᴱᵀ-algebraicity {A} {B} {τ} {τ'} =
      begin
           uncurryᵐ (enrᴱᵀ {A} {B} {τ + τ'})
        ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ {τ'})
      ≡⟨⟩
           uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ {τ'})
      ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ (delayᵀ τ {τ'})
      ≡⟨ ∘ᵐ-congʳ strᵀ-delayᵀ-algebraicity ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ delayᵀ τ
        ∘ᵐ [ τ ]ᶠ strᵀ
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (delayᵀ-nat _ _))) (∘ᵐ-assoc _ _ _)) ⟩
           delayᵀ τ
        ∘ᵐ [ τ ]ᶠ (Tᶠ (uncurryᵐ idᵐ))
        ∘ᵐ [ τ ]ᶠ strᵀ
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))) ⟩
           delayᵀ τ
        ∘ᵐ [ τ ]ᶠ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (sym (curryᵐ-uncurryᵐ-iso _)))) ⟩
           delayᵀ τ
        ∘ᵐ [ τ ]ᶠ (uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)))
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ (δ {A ⇒ᵐ B} {τ} {τ'}) idᵐ
      ≡⟨⟩
           delayᵀ τ
        ∘ᵐ [ τ ]ᶠ (uncurryᵐ (enrᴱᵀ {A} {B} {τ'}))
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ (δ {A ⇒ᵐ B} {τ} {τ'}) idᵐ
      ∎

    enrᴱᵀ-opᴱᵀ-algebraicity : ∀ {A B τ} (op : Op)
                            →    uncurryᵐ enrᴱᵀ
                              ∘ᵐ mapˣᵐ idᵐ (opᵀ op)
                            ≡    opᵀ op
                              ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {A} {B} {τ}))
                                                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                            ∘ᵐ []-monoidal ∘ᵐ mapˣᵐ δ idᵐ)
                              ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ

    enrᴱᵀ-opᴱᵀ-algebraicity {A} {B} {τ} op =
      begin
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ idᵐ (opᵀ op)
      ≡⟨⟩
           uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ))
        ∘ᵐ mapˣᵐ idᵐ (opᵀ op)
      ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ strᵀ
        ∘ᵐ mapˣᵐ idᵐ (opᵀ op)
      ≡⟨ ∘ᵐ-congʳ (strᵀ-opᵀ-algebraicity op) ⟩
           Tᶠ (uncurryᵐ idᵐ)
        ∘ᵐ opᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (opᵀ-nat op _))) (∘ᵐ-assoc _ _ _)) ⟩
           opᵀ op
        ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ))))
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (∘ᵐ-identityˡ _)
            refl)))) ⟩
           opᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ)))
              ∘ᵐ [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
          (begin
               [ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ)))
            ∘ᵐ [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ≡⟨ sym ([]-∘ᵐ _ _) ⟩
            [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ))
                             ∘ᵐ map⇒ᵐ idᵐ strᵀ
                             ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ≡⟨ cong [ op-time op ]ᶠ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
              (trans (sym (map⇒ᵐ-∘ᵐ _ _ _ _))
                (cong₂ map⇒ᵐ
                  (∘ᵐ-identityˡ _)
                  refl)))) ⟩
            [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
                             ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
          ∎))))) ⟩
           opᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
          (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (∘ᵐ-congˡ (cong₂ map⇒ᵐ refl (sym (curryᵐ-uncurryᵐ-iso _)))))))) ⟩
           opᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (curryᵐ (Tᶠ (uncurryᵐ idᵐ) ∘ᵐ strᵀ)))
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨⟩
           opᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {A} {B} {τ}))
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ∎
