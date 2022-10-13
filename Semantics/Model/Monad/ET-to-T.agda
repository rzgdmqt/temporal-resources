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
open import Semantics.Model.Modality.Future.Derived Cat Fut
open import Semantics.Model.Modality.Past.Derived Cat Pas
open import Semantics.Model.Modality.Adjunction.Derived Cat Fut Pas Adj

open import Semantics.Model.Monad Cat Fut Pas Adj Typ

open import Semantics.Model.Monad.Enriched Cat Fut Pas Adj Typ

-- Showing that [-]-strength follows from [-]-enrichment

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
              ; strᵀ-nat = strᴱᵀ-nat
              ; strᵀ-ηᵀ = strᵀ-ηᵀ
              ; strᵀ-μᵀ = strᵀ-μᵀ
              ; strᵀ-sndᵐ = strᵀ-sndᵐ
              ; strᵀ-assoc = strᵀ-assoc
              ; strᵀ-delayᵀ-algebraicity = strᵀ-delayᵀ-algebraicity
              ; strᵀ-opᵀ-algebraicity = λ op → strᵀ-opᵀ-algebraicity op
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
      ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
    
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
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (trans (trans (sym (uncurryᵐ-map⇒ᵐ _ _))
          (cong uncurryᵐ
            (trans
              (∘ᵐ-congˡ (cong₂ map⇒ᵐ (sym ET-idᵐ) refl))
              (enrᴱᵀ-nat _ _))))
          (uncurryᵐ-nat _ _))) (∘ᵐ-assoc _ _ _)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (map⇒ᵐ idᵐ sndᵐ)) idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))))
          (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (begin
                   ([]-≤ z≤n ∘ᵐ ε⁻¹)
                ∘ᵐ curryᵐ sndᵐ
                ∘ᵐ terminalᵐ
                ∘ᵐ sndᵐ
              ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                   []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ curryᵐ sndᵐ
                ∘ᵐ terminalᵐ
                ∘ᵐ sndᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ terminalᵐ-unique)) ⟩
                   []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ curryᵐ sndᵐ
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym ([]-ε⁻¹-nat _))) (∘ᵐ-assoc _ _ _))) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (curryᵐ sndᵐ)
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ 0 ]ᶠ (cong curryᵐ
                  (trans (sym (∘ᵐ-identityʳ _)) (∘ᵐ-congʳ (sym (curryᵐ-uncurryᵐ-iso _))))))) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (curryᵐ (   sndᵐ
                                   ∘ᵐ uncurryᵐ (curryᵐ idᵐ)))
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ 0 ]ᶠ (cong curryᵐ
                  (∘ᵐ-congʳ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _))))))) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (curryᵐ (   sndᵐ
                                   ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ)))
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ 0 ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (uncurryᵐ-nat _ _))))) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (curryᵐ (   sndᵐ
                                   ∘ᵐ uncurryᵐ idᵐ
                                   ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ))
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ 0 ]ᶠ
                  (trans (cong curryᵐ (sym (∘ᵐ-assoc _ _ _))) (curryᵐ-nat _ _)))) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (   curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ)
                           ∘ᵐ curryᵐ idᵐ)
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))))) ⟩
                   []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                ∘ᵐ [ 0 ]ᶠ (curryᵐ idᵐ)
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ trans (sym (∘ᵐ-assoc _ _ _))
                  (trans (∘ᵐ-congˡ (sym ([]-≤-nat _ _))) (∘ᵐ-assoc _ _ _)) ⟩
                   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                ∘ᵐ []-≤ z≤n
                ∘ᵐ [ 0 ]ᶠ (curryᵐ idᵐ)
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                  (trans (∘ᵐ-congˡ (sym ([]-≤-nat _ _))) (∘ᵐ-assoc _ _ _))) ⟩
                   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
                ∘ᵐ []-≤ z≤n
                ∘ᵐ ε⁻¹
                ∘ᵐ terminalᵐ
              ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ
                  (begin
                       []-≤ z≤n
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym terminalᵐ-unique)) ⟩
                       []-≤ z≤n
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
                       []-≤ z≤n
                    ∘ᵐ idᵐ
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ Gε⊣∘η⊣≡id))) ⟩
                       []-≤ z≤n
                    ∘ᵐ [ 0 ]ᶠ ε⊣
                    ∘ᵐ η⊣
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                      (sym ([]-≤-nat _ _))) (∘ᵐ-assoc _ _ _)) ⟩
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ []-≤ z≤n
                    ∘ᵐ η⊣
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-congˡ (sym η⊣-η-ε))
                      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩ 
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ η⁻¹
                    ∘ᵐ ε
                    ∘ᵐ η⊣
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                      (trans (∘ᵐ-congˡ η⊣≡ε⁻¹∘η) (∘ᵐ-assoc _ _ _)))))) ⟩ 
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ η⁻¹
                    ∘ᵐ ε
                    ∘ᵐ ε⁻¹
                    ∘ᵐ η
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                      (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ []-ε∘ε⁻¹≡id))))) ⟩ 
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ η⁻¹
                    ∘ᵐ idᵐ
                    ∘ᵐ η
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))) ⟩ 
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ η⁻¹
                    ∘ᵐ η
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-η⁻¹∘η≡id)))) ⟩ 
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ idᵐ
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) ⟩ 
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ ε⁻¹
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                      (trans (∘ᵐ-congˡ (sym (η⊣-nat _))) (∘ᵐ-assoc _ _ _)))) ⟩
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ ε⁻¹)
                    ∘ᵐ η⊣
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
                      (trans (sym ([]-∘ᵐ _ _)) (trans (cong [ τ ]ᶠ
                        (sym (⟨⟩-≤-nat _ _))) ([]-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ [ τ ]ᶠ (⟨ 0 ⟩ᶠ ε⁻¹)
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))) ⟩
                       [ τ ]ᶠ (ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ε⁻¹)
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ
                      (trans (∘ᵐ-congˡ ε⊣≡ε∘η⁻¹) (trans (∘ᵐ-assoc _ _ _)
                        (trans (∘ᵐ-congʳ (sym (⟨⟩-η⁻¹-nat _)))
                          (trans (sym (∘ᵐ-assoc _ _ _))
                            (trans (∘ᵐ-congˡ []-ε∘ε⁻¹≡id) (∘ᵐ-identityˡ _))))))) ⟩
                       [ τ ]ᶠ η⁻¹
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ η⊣
                    ∘ᵐ terminalᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
                      (trans (∘ᵐ-congˡ (sym (η⊣-nat _))) (∘ᵐ-assoc _ _ _)))) ⟩
                       [ τ ]ᶠ η⁻¹
                    ∘ᵐ [ τ ]ᶠ (⟨⟩-≤ z≤n)
                    ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ terminalᵐ)
                    ∘ᵐ η⊣
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ sym (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (trans (∘ᵐ-assoc _ _ _)
                      (∘ᵐ-congʳ (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))) ⟩
                       [ τ ]ᶠ (   η⁻¹
                               ∘ᵐ ⟨⟩-≤ z≤n
                               ∘ᵐ ⟨ τ ⟩ᶠ terminalᵐ)
                    ∘ᵐ η⊣
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (trans terminalᵐ-unique (sym terminalᵐ-unique))) ⟩
                       [ τ ]ᶠ ε⊣
                    ∘ᵐ η⊣
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ Gε⊣∘η⊣≡id) ⟩
                       idᵐ
                    ∘ᵐ [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ≡⟨ ∘ᵐ-identityˡ _ ⟩
                       [ τ ]ᶠ terminalᵐ
                    ∘ᵐ fstᵐ
                  ∎)) ⟩
                   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
                ∘ᵐ [ τ ]ᶠ terminalᵐ
                ∘ᵐ fstᵐ
              ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
                   (   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                    ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
                    ∘ᵐ [ τ ]ᶠ terminalᵐ)
                ∘ᵐ fstᵐ
              ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym ([]-∘ᵐ _ _))
                  (sym (trans (∘ᵐ-congʳ (sym ([]-∘ᵐ _ _))) (trans (sym ([]-∘ᵐ _ _))
                    (cong [ τ ]ᶠ (
                      begin
                           curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ)
                        ∘ᵐ curryᵐ idᵐ
                        ∘ᵐ terminalᵐ
                      ≡⟨ ∘ᵐ-congʳ (sym (curryᵐ-nat _ _)) ⟩
                           curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ)
                        ∘ᵐ curryᵐ (idᵐ ∘ᵐ mapˣᵐ terminalᵐ idᵐ)
                      ≡⟨ ∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-identityˡ _)) ⟩
                           curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ)
                        ∘ᵐ curryᵐ (mapˣᵐ terminalᵐ idᵐ)
                      ≡⟨ trans (sym (curryᵐ-nat _ _)) (cong curryᵐ (∘ᵐ-assoc _ _ _)) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ uncurryᵐ idᵐ
                                ∘ᵐ mapˣᵐ (curryᵐ (mapˣᵐ terminalᵐ idᵐ)) idᵐ)
                      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (uncurryᵐ-nat _ _)))  ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ (mapˣᵐ terminalᵐ idᵐ)))
                      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (cong uncurryᵐ (∘ᵐ-identityˡ _))) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ uncurryᵐ (curryᵐ (mapˣᵐ terminalᵐ idᵐ)))
                      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (curryᵐ-uncurryᵐ-iso _)) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ mapˣᵐ terminalᵐ idᵐ)
                      ≡⟨ cong curryᵐ (trans (⟨⟩ᵐ-sndᵐ _ _) (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ idᵐ)
                      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (curryᵐ-uncurryᵐ-iso _))) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ uncurryᵐ (curryᵐ idᵐ))
                      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _)))) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ))
                      ≡⟨ cong curryᵐ (∘ᵐ-congʳ (uncurryᵐ-nat _ _)) ⟩
                        curryᵐ (   sndᵐ
                                ∘ᵐ uncurryᵐ idᵐ
                                ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ)
                      ≡⟨ trans (cong curryᵐ (sym (∘ᵐ-assoc _ _ _))) (curryᵐ-nat _ _) ⟩
                           curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ)
                        ∘ᵐ curryᵐ idᵐ
                      ∎)))))))) ⟩
                   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
                ∘ᵐ fstᵐ
              ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                   (   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ))
                    ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
                ∘ᵐ fstᵐ
              ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (cong [ τ ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
                  (trans (sym (∘ᵐ-identityʳ _)) (∘ᵐ-congʳ (sym mapˣᵐ-identity))))))) ⟩
                   (   [ τ ]ᶠ (curryᵐ (sndᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ))
                    ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
                ∘ᵐ fstᵐ
              ∎)
              (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _))))))))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([]-≤ z≤n ∘ᵐ ε⁻¹) idᵐ
        ∘ᵐ mapˣᵐ {𝟙ᵐ} (curryᵐ sndᵐ) idᵐ
        ∘ᵐ ⟨ terminalᵐ , idᵐ ⟩ᵐ
        ∘ᵐ sndᵐ
      ≡⟨ sym (trans (∘ᵐ-congˡ (sym (enrᴱᵀ-idᵐ))) (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
           sndᵐ
        ∘ᵐ ⟨ terminalᵐ , idᵐ ⟩ᵐ
        ∘ᵐ sndᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _)) ⟩
        sndᵐ
      ∎

    strᵀ-assoc : ∀ {A B C τ}
               →    ETᶠ ×ᵐ-assoc
                 ∘ᵐ strᴱᵀ
                 ∘ᵐ mapˣᵐ []-monoidal idᵐ
                 ∘ᵐ ×ᵐ-assoc⁻¹
               ≡    strᴱᵀ {A} {B ×ᵐ C} {τ}
                 ∘ᵐ mapˣᵐ idᵐ strᴱᵀ
    strᵀ-assoc {A} {B} {C} {τ} = 
      begin
           ETᶠ ×ᵐ-assoc
        ∘ᵐ strᴱᵀ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
           ETᶠ ×ᵐ-assoc
        ∘ᵐ uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-map⇒ᵐ _ _))) ⟩
           uncurryᵐ (   map⇒ᵐ idᵐ (ETᶠ ×ᵐ-assoc)
                     ∘ᵐ enrᴱᵀ)
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congˡ (cong₂ map⇒ᵐ (sym ET-idᵐ) refl))) ⟩
           uncurryᵐ (   map⇒ᵐ (ETᶠ idᵐ) (ETᶠ ×ᵐ-assoc)
                     ∘ᵐ enrᴱᵀ)
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (enrᴱᵀ-nat _ _)) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ ×ᵐ-assoc))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ (×ᵐ-assoc ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ)))
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (uncurryᵐ-nat _ _))
          (cong uncurryᵐ (∘ᵐ-assoc _ _ _)))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ (×ᵐ-assoc ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ))
                     ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ))
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (sym ([]-∘ᵐ _ _)))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ (×ᵐ-assoc ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ) ∘ᵐ curryᵐ idᵐ))
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ (∘ᵐ-congˡ (cong curryᵐ
         (trans (∘ᵐ-congʳ (∘ᵐ-congʳ mapˣᵐ-identity)) (∘ᵐ-congʳ (∘ᵐ-identityʳ _)))))))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ (×ᵐ-assoc ∘ᵐ uncurryᵐ idᵐ) ∘ᵐ curryᵐ idᵐ))
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ
          (trans (sym (curryᵐ-nat _ _)) (cong curryᵐ (∘ᵐ-assoc _ _ _)))))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ (×ᵐ-assoc ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ)))
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (sym (uncurryᵐ-nat _ _))))))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ (×ᵐ-assoc ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ))))
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ
          (trans (∘ᵐ-congʳ (cong uncurryᵐ (∘ᵐ-identityˡ _)))
            (trans (∘ᵐ-congʳ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-identityʳ _))))))) ⟩
           uncurryᵐ (   enrᴱᵀ
                     ∘ᵐ [ τ ]ᶠ (curryᵐ ×ᵐ-assoc))
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _)))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ ×ᵐ-assoc))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ
          (sym (∘ᵐ-identityˡ _)))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   idᵐ
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ
          (sym (trans (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-identityˡ _)))
            (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)))))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ)
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ
          (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _))))))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ
          (∘ᵐ-congʳ (∘ᵐ-congˡ
            (cong₂ mapˣᵐ refl
              (sym (trans (cong uncurryᵐ (∘ᵐ-identityˡ _)) (curryᵐ-uncurryᵐ-iso _)))))))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ (curryᵐ idᵐ) (uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ))
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ
          (∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (uncurryᵐ-nat _ _)))))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ (curryᵐ idᵐ) (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ)
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
          (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
            (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityˡ _) (sym (∘ᵐ-assoc _ _ _)))))))))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ idᵐ appᵐ
                             ∘ᵐ mapˣᵐ (curryᵐ idᵐ) (mapˣᵐ (curryᵐ idᵐ) idᵐ)
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (cong curryᵐ
          (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
             (cong₂ ⟨_,_⟩ᵐ
               (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                 (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-assoc _ _ _)))))
               (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                 (cong₂ ⟨_,_⟩ᵐ
                   (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                     (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
                   (trans (∘ᵐ-identityˡ _) (sym (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)))))))))))))))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ idᵐ appᵐ
                             ∘ᵐ ×ᵐ-assoc
                             ∘ᵐ mapˣᵐ (mapˣᵐ (curryᵐ idᵐ) (curryᵐ idᵐ)) idᵐ)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (cong [ τ ]ᶠ (trans (cong curryᵐ
          (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) (curryᵐ-nat _ _))) refl)) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (   curryᵐ (   appᵐ
                                ∘ᵐ mapˣᵐ idᵐ appᵐ
                                ∘ᵐ ×ᵐ-assoc)
                     ∘ᵐ mapˣᵐ (curryᵐ idᵐ) (curryᵐ idᵐ)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ (sym ([]-∘ᵐ _ _)) (∘ᵐ-identityˡ _)))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ idᵐ appᵐ
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (mapˣᵐ (curryᵐ idᵐ) (curryᵐ idᵐ))) idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans
          (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ (sym ([]-monoidal-nat _ _)) refl))))) (∘ᵐ-assoc _ _ _)))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ idᵐ appᵐ
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ mapˣᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) ([ τ ]ᶠ (curryᵐ idᵐ))) idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (sym (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
            (cong₂ ⟨_,_⟩ᵐ
              (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                (cong₂ ⟨_,_⟩ᵐ
                  (sym (trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-congˡ (∘ᵐ-identityʳ _))))
                  (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                    (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                      (⟨⟩ᵐ-fstᵐ _ _))) (∘ᵐ-assoc _ _ _))))))))))
              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (sym (∘ᵐ-assoc _ _ _))
                (trans (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (⟨⟩ᵐ-sndᵐ _ _))) (∘ᵐ-assoc _ _ _)))))))))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ
            ([ τ ]ᶠ (curryᵐ (   appᵐ
                             ∘ᵐ mapˣᵐ idᵐ appᵐ
                             ∘ᵐ ×ᵐ-assoc)))
            idᵐ
        ∘ᵐ mapˣᵐ []-monoidal idᵐ
        ∘ᵐ ×ᵐ-assoc⁻¹
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
      ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ enrᴱᵀ-idᵐ-∘ᵐ)
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ enrᴱᵀ)
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ
              (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
              (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))))))
            (∘ᵐ-assoc _ _ _))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ enrᴱᵀ)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans
          (cong₂ mapˣᵐ
            (sym (∘ᵐ-identityˡ _)) refl)
            (mapˣᵐ-∘ᵐ _ _ _ _)))) ⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
      ≡⟨⟩
           uncurryᵐ enrᴱᵀ
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ strᴱᵀ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           strᴱᵀ
        ∘ᵐ mapˣᵐ idᵐ strᴱᵀ
      ∎
    

    strᵀ-delayᵀ-algebraicity : ∀ {A B τ τ'}
                             →    strᴱᵀ {A} {B} {τ + τ'}
                               ∘ᵐ mapˣᵐ idᵐ (delayᴱᵀ τ {τ'})
                             ≡    delayᴱᵀ τ
                               ∘ᵐ [ τ ]ᶠ (strᴱᵀ {A} {B} {τ'})
                               ∘ᵐ []-monoidal
                               ∘ᵐ mapˣᵐ (δ {A} {τ} {τ'}) idᵐ

    strᵀ-delayᵀ-algebraicity {A} {B} {τ} {τ'} =
      begin
           strᴱᵀ {A} {B} {τ + τ'}
        ∘ᵐ mapˣᵐ idᵐ (delayᴱᵀ τ {τ'})
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ + τ'})
        ∘ᵐ mapˣᵐ ([ τ + τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ (delayᴱᵀ τ {τ'})
      ≡⟨ ∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))
            (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _))))))) ⟩
           uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ + τ'})
        ∘ᵐ mapˣᵐ idᵐ (delayᴱᵀ τ {τ'})
        ∘ᵐ mapˣᵐ ([ τ + τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ enrᴱᵀ-delayᴱᵀ-algebraicity) ⟩
           (   delayᴱᵀ τ
            ∘ᵐ [ τ ]ᶠ (uncurryᵐ enrᴱᵀ)
            ∘ᵐ []-monoidal
            ∘ᵐ mapˣᵐ δ idᵐ)
            ∘ᵐ mapˣᵐ ([ τ + τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
           delayᴱᵀ τ
        ∘ᵐ [ τ ]ᶠ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ'}))
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ δ idᵐ
        ∘ᵐ mapˣᵐ ([ τ + τ' ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ ([]-δ-nat _) (∘ᵐ-congˡ []-idᵐ))))))) ⟩
           delayᴱᵀ τ
        ∘ᵐ [ τ ]ᶠ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ'}))
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ ([ τ ]ᶠ ([ τ' ]ᶠ (curryᵐ idᵐ))) ([ τ ]ᶠ idᵐ)
        ∘ᵐ mapˣᵐ (δ {A} {τ} {τ'}) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans
          (∘ᵐ-congˡ (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _)))) ⟩
           delayᴱᵀ τ
        ∘ᵐ [ τ ]ᶠ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ'}))
        ∘ᵐ [ τ ]ᶠ (mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ (δ {A} {τ} {τ'}) idᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))) ⟩
           delayᴱᵀ τ
        ∘ᵐ [ τ ]ᶠ (   uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ'})
                   ∘ᵐ mapˣᵐ ([ τ' ]ᶠ (curryᵐ idᵐ)) idᵐ)
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ (δ {A} {τ} {τ'}) idᵐ
      ≡⟨⟩
           delayᴱᵀ τ
        ∘ᵐ [ τ ]ᶠ (strᴱᵀ {A} {B} {τ'})
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ (δ {A} {τ} {τ'}) idᵐ
      ∎

    strᵀ-opᵀ-algebraicity : ∀ {A B τ } (op : Op)
                          →    strᴱᵀ {A} {B}
                            ∘ᵐ mapˣᵐ idᵐ (opᴱᵀ op)
                          ≡    opᴱᵀ op
                            ∘ᵐ mapˣᵐ idᵐ ([ op-time op ]ᶠ (   map⇒ᵐ idᵐ (strᴱᵀ {A} {B} {τ})
                                                           ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                                           ∘ᵐ []-monoidal
                                                           ∘ᵐ mapˣᵐ δ idᵐ)
                            ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    strᵀ-opᵀ-algebraicity {A} {B} {τ} op = 
      begin
           strᴱᵀ {A} {B}
        ∘ᵐ mapˣᵐ idᵐ (opᴱᵀ op)
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {op-time op + τ})
        ∘ᵐ mapˣᵐ ([ op-time op + τ ]ᶠ (curryᵐ idᵐ)) idᵐ
        ∘ᵐ mapˣᵐ idᵐ (opᴱᵀ op)
      ≡⟨ ∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))
            (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _))))))) ⟩
           uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {op-time op + τ})
        ∘ᵐ mapˣᵐ idᵐ (opᴱᵀ op)
        ∘ᵐ mapˣᵐ ([ op-time op + τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (enrᴱᵀ-opᴱᵀ-algebraicity op)) ⟩
           (   opᴱᵀ op
            ∘ᵐ mapˣᵐ
                 idᵐ
                 (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                      ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                  ∘ᵐ []-monoidal
                  ∘ᵐ mapˣᵐ δ idᵐ)
            ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
        ∘ᵐ mapˣᵐ ([ op-time op + τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ mapˣᵐ ([ op-time op + τ ]ᶠ (curryᵐ idᵐ)) idᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ
            (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
              (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (sym (∘ᵐ-identityˡ _))))))
            (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (⟨⟩ᵐ-fstᵐ _ _)
                (trans
                  (∘ᵐ-assoc _ _ _)
                  (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                    (sym (∘ᵐ-identityˡ _)))))))))))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ ([ op-time op + τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
          (cong₂ mapˣᵐ
            (∘ᵐ-identityˡ _)
            (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ
              ∘ᵐ mapˣᵐ ([ op-time op + τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
          (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ ([]-δ-nat _) (∘ᵐ-congˡ []-idᵐ))))))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ ([ op-time op ]ᶠ ([ τ ]ᶠ (curryᵐ idᵐ))) ([ op-time op ]ᶠ idᵐ)
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
          (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
            (sym ([]-monoidal-nat _ _))) (∘ᵐ-assoc _ _ _)))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
              ∘ᵐ [ op-time op ]ᶠ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
          (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym ([]-∘ᵐ _ _))
            (cong [ op-time op ]ᶠ (∘ᵐ-assoc _ _ _))))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}))
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                  ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   curryᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}) ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ)
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                  ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (∘ᵐ-congˡ
          (cong [ op-time op ]ᶠ (∘ᵐ-congˡ (cong curryᵐ (∘ᵐ-congʳ
            (trans (∘ᵐ-congʳ mapˣᵐ-identity) (∘ᵐ-identityʳ _))))))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ
             idᵐ
             (   [ op-time op ]ᶠ (   curryᵐ (uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ}) ∘ᵐ uncurryᵐ idᵐ)
                                  ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                  ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
          (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (
            begin
                 curryᵐ (uncurryᵐ enrᴱᵀ ∘ᵐ uncurryᵐ idᵐ)
              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
              ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
            ≡⟨ ∘ᵐ-congʳ (sym (curryᵐ-nat _ _)) ⟩
                 curryᵐ (uncurryᵐ enrᴱᵀ ∘ᵐ uncurryᵐ idᵐ)
              ∘ᵐ curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                         ∘ᵐ mapˣᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ) idᵐ)
            ≡⟨ trans (sym (curryᵐ-nat _ _)) (cong curryᵐ (∘ᵐ-assoc _ _ _)) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ uncurryᵐ idᵐ
                      ∘ᵐ mapˣᵐ (curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                        ∘ᵐ mapˣᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ) idᵐ))
                               idᵐ)
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (uncurryᵐ-nat _ _))) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ uncurryᵐ (   idᵐ
                                   ∘ᵐ (curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                               ∘ᵐ mapˣᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ) idᵐ))))
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (cong uncurryᵐ (∘ᵐ-identityˡ _))) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ uncurryᵐ (curryᵐ (   ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ mapˣᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ) idᵐ)))
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (curryᵐ-uncurryᵐ-iso _)) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                      ∘ᵐ mapˣᵐ (mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ) idᵐ)
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym
                (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (cong₂ ⟨_,_⟩ᵐ
                    (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
                    (trans (∘ᵐ-identityˡ _) (sym (trans (sym (uncurryᵐ-nat _ _))
                      (cong uncurryᵐ (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))))))))) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
                      ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (curryᵐ-uncurryᵐ-iso _)))) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
                      ∘ᵐ uncurryᵐ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _))))) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
                      ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (uncurryᵐ-nat _ _))) ⟩
              curryᵐ (   uncurryᵐ enrᴱᵀ
                      ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
                      ∘ᵐ uncurryᵐ idᵐ
                      ∘ᵐ mapˣᵐ (curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ) idᵐ)
            ≡⟨ sym (trans (sym (curryᵐ-nat _ _)) (cong curryᵐ
                (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
                 curryᵐ (   uncurryᵐ enrᴱᵀ
                         ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
                         ∘ᵐ uncurryᵐ idᵐ)
              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congˡ (cong curryᵐ (sym (∘ᵐ-assoc _ _ _))) ⟩
                 curryᵐ (   (uncurryᵐ enrᴱᵀ ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
                         ∘ᵐ uncurryᵐ idᵐ)
              ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
            ∎))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   curryᵐ (   (   uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ})
                                                         ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
                                                     ∘ᵐ uncurryᵐ idᵐ)
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal
                      ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (∘ᵐ-congˡ
          (cong [ op-time op ]ᶠ (∘ᵐ-congˡ (cong curryᵐ (∘ᵐ-congʳ
            (sym (trans (∘ᵐ-congʳ mapˣᵐ-identity) (∘ᵐ-identityʳ _)))))))))) ⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   curryᵐ (   (   uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ})
                                                         ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
                                                     ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ)
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal
                      ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (   uncurryᵐ (enrᴱᵀ {B} {A ×ᵐ B} {τ})
                                                        ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal
                      ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨⟩
           opᴱᵀ op
        ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ (strᴱᵀ {A} {B} {τ})
                                          ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ []-monoidal
                      ∘ᵐ mapˣᵐ δ idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ∎

