-----------------------------------------------------------------------------
-- Strong (via enrichment) graded monad equipped with algebraic operations --
-----------------------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction
open import Semantics.Model.BaseGroundTypes

module Semantics.Model.Monad.ET-to-T (Cat : Category)
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

open import Semantics.Model.Monad Cat Fut Pas Adj Typ

open import Semantics.Model.Monad.Enriched Cat Fut Pas Adj Typ

-- Showing that the [-]-strength follows from [-]-enrichment

ET-to-T : EMonad → Monad
ET-to-T M = record
              { Tᵒ = ETᵒ
              ; Tᶠ = ETᶠ
              ; ηᵀ = ηᴱᵀ
              ; μᵀ = μᴱᵀ
              ; τ-substᵀ = τ-substᴱᵀ
              ; τ-substᵀ-refl = τ-substᴱᵀ-refl
              ; τ-substᵀ-trans = τ-substᴱᵀ-trans
              ; T-idᵐ = ET-idᵐ
              ; T-∘ᵐ = ET-∘ᵐ
              ; ηᵀ-nat = ηᴱᵀ-nat
              ; μᵀ-nat = μᴱᵀ-nat
              ; T-μ∘η≡id = ET-μ∘η≡id
              ; T-μ∘Tη≡id = ET-μ∘ETη≡id
              ; T-μ∘μ≡μ∘Tμ = ET-μ∘μ≡μ∘ETμ
              ; delayᵀ = delayᴱᵀ
              ; opᵀ = opᴱᵀ
              ; delayᵀ-nat = delayᴱᵀ-nat
              ; opᵀ-nat = opᴱᵀ-nat
              ; delayᵀ-algebraicity = delayᴱᵀ-algebraicity
              ; opᵀ-algebraicity = opᴱᵀ-algebraicity
              ; strᵀ = strᴱᵀ
              ; strᵀ-nat = {!!} -- strᴱᵀ-nat
              ; strᵀ-ηᵀ = {!!} --strᵀ-ηᵀ
              ; strᵀ-μᵀ = {!!} --strᵀ-μᵀ
              ; strᵀ-sndᵐ = ? --strᵀ-sndᵐ
              ; strᵀ-assoc = {!!}
              ; strᵀ-delayᵀ-algebraicity = {!!}
              ; strᵀ-opᵀ-algebraicity = {!!}
              ; T-alg-of-handlerᵀ = ET-alg-of-handlerᴱᵀ
              ; T-alg-of-handlerᵀ-ηᵀ = ET-alg-of-handlerᴱᵀ-ηᴱᵀ
              ; T-alg-of-handlerᵀ-delayᵀ = ET-alg-of-handlerᴱᵀ-delayᴱᵀ
              ; T-alg-of-handlerᵀ-opᵀ = ET-alg-of-handlerᴱᵀ-opᴱᵀ
              }
  where

    open EMonad M

    
    strᴱᵀ : ∀ {A B τ} → [ τ ]ᵒ A ×ᵐ ETᵒ B τ →ᵐ ETᵒ (A ×ᵐ B) τ
    strᴱᵀ {A} {B} {τ} =
         uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ})
      ∘ᵐ mapˣᵐ
          ([ τ ]ᶠ (curryᵐ idᵐ))
          idᵐ
    {-
    strᴱᵀ-nat : ∀ {A B C D τ}
              → (f : A →ᵐ B)
              → (g : C →ᵐ D)
              → strᴱᵀ ∘ᵐ mapˣᵐ ([ τ ]ᶠ f) (ETᶠ g)
              ≡ ETᶠ (mapˣᵐ f g) ∘ᵐ strᴱᵀ
    strᴱᵀ-nat {A} {B} {C} {D} {τ} f g =
      begin
           strᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ f) (ETᶠ g)
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ f) (ETᶠ g)
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ f) (ETᶠ g)
      ≡⟨ trans
          (sym (uncurryᵐ-mapˣᵐ _ _ _))
          (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
        uncurryᵐ
          (   map⇒ᵐ (ETᶠ g) idᵐ
           ∘ᵐ enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
           ∘ᵐ [ τ ]ᶠ f)
      ≡⟨ cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym ([]-∘ᵐ _ _)))) ⟩
        uncurryᵐ
          (   map⇒ᵐ (ETᶠ g) idᵐ
           ∘ᵐ enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ ∘ᵐ f))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congˡ (cong₂ map⇒ᵐ refl (sym ET-idᵐ))) ⟩
        uncurryᵐ
          (   map⇒ᵐ (ETᶠ g) (ETᶠ idᵐ)
           ∘ᵐ enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ ∘ᵐ f))
      ≡⟨ cong uncurryᵐ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans
            (∘ᵐ-congˡ (enrᴱᵀ-nat _ _))
            (∘ᵐ-assoc _ _ _))) ⟩
        uncurryᵐ
          (   enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (map⇒ᵐ g idᵐ)
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ ∘ᵐ f))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congʳ (sym ([]-∘ᵐ _ _))) ⟩
        uncurryᵐ
          (   enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (map⇒ᵐ g idᵐ ∘ᵐ curryᵐ idᵐ ∘ᵐ f))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ (sym (curryᵐ-mapˣᵐ _ _ _)))) ⟩
        uncurryᵐ
          (   enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ (idᵐ ∘ᵐ mapˣᵐ f g)))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ
          (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))))) ⟩
        uncurryᵐ
          (   enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ (mapˣᵐ f g ∘ᵐ idᵐ)))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ (curryᵐ-map⇒ᵐ _ _))) ⟩
        uncurryᵐ
          (   enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (mapˣᵐ f g) ∘ᵐ curryᵐ idᵐ))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congʳ ([]-∘ᵐ _ _)) ⟩
        uncurryᵐ
          (   enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (mapˣᵐ f g))
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
      ≡⟨ cong uncurryᵐ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (sym (enrᴱᵀ-nat _ _))) (∘ᵐ-assoc _ _ _))) ⟩
        uncurryᵐ
          (   map⇒ᵐ (ETᶠ idᵐ) (ETᶠ (mapˣᵐ f g))
           ∘ᵐ enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
      ≡⟨ cong uncurryᵐ (∘ᵐ-congˡ (cong₂ map⇒ᵐ ET-idᵐ refl)) ⟩
        uncurryᵐ
          (   map⇒ᵐ idᵐ (ETᶠ (mapˣᵐ f g))
           ∘ᵐ enrᴱᵀ
           ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
      ≡⟨ uncurryᵐ-map⇒ᵐ _ _ ⟩
           ETᶠ (mapˣᵐ f g)
        ∘ᵐ uncurryᵐ
             (   enrᴱᵀ
              ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
      ≡⟨ ∘ᵐ-congʳ (cong uncurryᵐ (sym (trans (∘ᵐ-congˡ map⇒ᵐ-identity) (∘ᵐ-identityˡ _)))) ⟩
           ETᶠ (mapˣᵐ f g)
        ∘ᵐ uncurryᵐ
             (   map⇒ᵐ idᵐ idᵐ
              ∘ᵐ enrᴱᵀ
              ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
      ≡⟨ ∘ᵐ-congʳ (uncurryᵐ-mapˣᵐ _ _ _) ⟩
           ETᶠ (mapˣᵐ f g)
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨⟩
           ETᶠ (mapˣᵐ f g)
        ∘ᵐ strᴱᵀ
      ∎
    
    strᵀ-ηᵀ : ∀ {A B}
            → strᴱᵀ {A} {B} {0} ∘ᵐ mapˣᵐ ε⁻¹ ηᴱᵀ ≡ ηᴱᵀ
    strᵀ-ηᵀ {A} {B} = 
      begin
          strᴱᵀ
       ∘ᵐ mapˣᵐ ε⁻¹ ηᴱᵀ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ 0 ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ ε⁻¹ ηᴱᵀ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (sym ([]-ε⁻¹-nat _))
            (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _))))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ε⁻¹ ηᴱᵀ
        ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ enrᴱᵀ-ηᴱᵀ) (∘ᵐ-assoc _ _ _)) ⟩
           ηᴱᵀ
        ∘ᵐ uncurryᵐ idᵐ
        ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (uncurryᵐ-nat _ _)) ⟩
           ηᴱᵀ
        ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ)
      ≡⟨ ∘ᵐ-congʳ (cong uncurryᵐ (∘ᵐ-identityˡ _)) ⟩
           ηᴱᵀ
        ∘ᵐ uncurryᵐ (curryᵐ idᵐ)
      ≡⟨ ∘ᵐ-congʳ (curryᵐ-uncurryᵐ-iso _) ⟩
           ηᴱᵀ
        ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        ηᴱᵀ
      ∎

    strᵀ-μᵀ : ∀ {A B τ τ'}
            → μᴱᵀ {A ×ᵐ B} {τ} {τ'} ∘ᵐ ETᶠ strᴱᵀ ∘ᵐ strᴱᵀ
            ≡ strᴱᵀ ∘ᵐ mapˣᵐ δ⁻¹ μᴱᵀ
    strᵀ-μᵀ {A} {B} {τ} {τ'} =
      begin
           μᴱᵀ
        ∘ᵐ ETᶠ strᴱᵀ
        ∘ᵐ strᴱᵀ
      ≡⟨⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (   uncurryᵐ enrᴱᵀ
                ∘ᵐ mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ)
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (ET-∘ᵐ _ _))))) ⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (uncurryᵐ enrᴱᵀ)
        ∘ᵐ ETᶠ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ)
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-map⇒ᵐ _ _))))) ⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (uncurryᵐ enrᴱᵀ)
        ∘ᵐ uncurryᵐ (   map⇒ᵐ idᵐ (ETᶠ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
                     ∘ᵐ enrᴱᵀ)
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (uncurryᵐ-nat _ _)) (cong uncurryᵐ (∘ᵐ-assoc _ _ _)))) ⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (uncurryᵐ enrᴱᵀ)
        ∘ᵐ uncurryᵐ (   map⇒ᵐ idᵐ (ETᶠ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
                     ∘ᵐ enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong uncurryᵐ (
          begin
               map⇒ᵐ idᵐ (ETᶠ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
            ∘ᵐ enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
          ≡⟨ ∘ᵐ-congˡ (cong₂ map⇒ᵐ (sym ET-idᵐ) refl) ⟩
               map⇒ᵐ (ETᶠ idᵐ) (ETᶠ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
            ∘ᵐ enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
          ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (enrᴱᵀ-nat _ _)) (∘ᵐ-assoc _ _ _)) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
            ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
          ≡⟨ ∘ᵐ-congʳ (sym ([]-∘ᵐ _ _)) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ) ∘ᵐ curryᵐ idᵐ)
          ≡⟨⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (   curryᵐ (   mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
                                  ∘ᵐ uncurryᵐ idᵐ
                                  ∘ᵐ mapˣᵐ idᵐ idᵐ)
                       ∘ᵐ curryᵐ idᵐ)
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (∘ᵐ-congˡ (cong curryᵐ (∘ᵐ-congʳ
              (trans (∘ᵐ-congʳ mapˣᵐ-identity) (∘ᵐ-identityʳ _)))))) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (   curryᵐ (   mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
                                  ∘ᵐ uncurryᵐ idᵐ)
                       ∘ᵐ curryᵐ idᵐ)
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (trans (sym (curryᵐ-nat _ _)) (cong curryᵐ (∘ᵐ-assoc _ _ _)))) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ (   mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
                               ∘ᵐ uncurryᵐ idᵐ
                               ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ))
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (sym (uncurryᵐ-nat _ _))))) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ (   mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
                               ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ)))
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (cong uncurryᵐ (∘ᵐ-identityˡ _))))) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ (   mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
                               ∘ᵐ uncurryᵐ (curryᵐ idᵐ)))
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ (trans (∘ᵐ-congʳ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-identityʳ _)))) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ (sym (∘ᵐ-identityˡ _)))) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ (idᵐ ∘ᵐ mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ))
          ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (curryᵐ-nat _ _)) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ ∘ᵐ [ τ' ]ᶠ (curryᵐ idᵐ))
          ≡⟨ ∘ᵐ-congʳ ([]-∘ᵐ _ _) ⟩
               enrᴱᵀ
            ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
            ∘ᵐ [ τ ]ᶠ ([ τ' ]ᶠ (curryᵐ idᵐ))
          ∎))) ⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (uncurryᵐ (enrᴱᵀ ))
        ∘ᵐ uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ) ∘ᵐ [ τ ]ᶠ ([ τ' ]ᶠ (curryᵐ idᵐ)))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (uncurryᵐ-nat _ _)) ⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (uncurryᵐ (enrᴱᵀ ))
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ) ∘ᵐ [ τ ]ᶠ ([ τ' ]ᶠ (curryᵐ idᵐ))) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ refl (∘ᵐ-identityˡ _)))))) ⟩
           μᴱᵀ
        ∘ᵐ ETᶠ (uncurryᵐ (enrᴱᵀ ))
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (curryᵐ idᵐ))) idᵐ
      ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym enrᴱᵀ-μᴱᵀ))
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ δ⁻¹ μᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (curryᵐ idᵐ))) idᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            ([]-δ⁻¹-nat _)
            (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ + τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ δ⁻¹ μᴱᵀ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           strᴱᵀ
        ∘ᵐ mapˣᵐ δ⁻¹ μᴱᵀ
      ∎

    strᵀ-sndᵐ : ∀ {A B τ}
              → ETᶠ sndᵐ ∘ᵐ strᴱᵀ {A} {B} {τ} ≡ sndᵐ
    strᵀ-sndᵐ {A} {B} {τ} = 
      begin
           ETᶠ sndᵐ
        ∘ᵐ strᴱᵀ
      ≡⟨⟩
           ETᶠ sndᵐ
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ enrᴱᵀ-sndᵐ) ⟩
           sndᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ⟨⟩ᵐ-sndᵐ _ _ ⟩
        idᵐ ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-identityˡ _ ⟩
        sndᵐ
      ∎
    -}

