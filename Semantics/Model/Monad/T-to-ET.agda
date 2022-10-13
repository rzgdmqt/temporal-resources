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
              ; enrᴱᵀ-nat = {!!} --enrᴱᵀ-nat
              ; enrᴱᵀ-ηᴱᵀ = {!!} --enrᴱᵀ-ηᴱᵀ
              ; enrᴱᵀ-μᴱᵀ = {!!}
              ; enrᴱᵀ-idᵐ = {!!}
              ; enrᴱᵀ-idᵐ-∘ᵐ = {!!}
              ; enrᴱᵀ-delayᴱᵀ-algebraicity = {!!}
              ; enrᴱᵀ-opᴱᵀ-algebraicity = {!!}
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

    {-
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
    -}

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
        ∘ᵐ uncurryᵐ enrᴱᵀ ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ {!!} ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ δ⁻¹ μᵀ
      ∎


{-

    enrᴱᵀ : ∀ {A B τ} → [ τ ]ᵒ (A ⇒ᵐ B) →ᵐ Tᵒ A τ ⇒ᵐ Tᵒ B τ
    enrᴱᵀ {A} {B} {τ} =
      curryᵐ (   Tᶠ (uncurryᵐ idᵐ)
              ∘ᵐ strᵀ)

-}
