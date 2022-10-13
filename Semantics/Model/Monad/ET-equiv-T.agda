-----------------------------------------------------------------------------
-- Strong (via enrichment) graded monad equipped with algebraic operations --
-----------------------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction
open import Semantics.Model.BaseGroundTypes

module Semantics.Model.Monad.ET-equiv-T (Cat : Category)
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

open import Semantics.Model.Monad.ET-to-T Cat Fut Pas Adj Typ
open import Semantics.Model.Monad.T-to-ET Cat Fut Pas Adj Typ

open Monad
open EMonad

-- Showing that the mappings between [-]-strong and [-]-enriched
-- graded monads form an isomorphism. For this, we prove that the
-- translatioins between strᵀ and enrᴱᵀ form an isomorphism---the
-- rest of the structure is mapped by identity, and equality
-- proofs will be trivially equal via UIP (see _≡ᵗ_ as example).

T-to-ET-to-T : ∀ {A B τ}
             → (M : Monad)
             → strᵀ (ET-to-T (T-to-ET M)) {A} {B} {τ}
             ≡ strᵀ M

T-to-ET-to-T {A} {B} {τ} M =
  begin
    strᵀ (ET-to-T (T-to-ET M)) {A} {B} {τ}
  ≡⟨⟩
       uncurryᵐ (curryᵐ (Tᶠ M (uncurryᵐ idᵐ) ∘ᵐ strᵀ M))
    ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
  ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
       Tᶠ M (uncurryᵐ idᵐ)
    ∘ᵐ strᵀ M
    ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ mapˣᵐ refl (sym (T-idᵐ M)))) ⟩
       Tᶠ M (uncurryᵐ idᵐ)
    ∘ᵐ strᵀ M
    ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) (Tᶠ M idᵐ)
  ≡⟨ ∘ᵐ-congʳ (strᵀ-nat M _ _) ⟩
       Tᶠ M (uncurryᵐ idᵐ)
    ∘ᵐ Tᶠ M (mapˣᵐ (curryᵐ idᵐ) idᵐ)
    ∘ᵐ strᵀ M
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (T-∘ᵐ M _ _) )) ⟩
       Tᶠ M (   uncurryᵐ idᵐ
             ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ)
    ∘ᵐ strᵀ M
  ≡⟨ ∘ᵐ-congˡ (cong (Tᶠ M) (sym (uncurryᵐ-nat _ _))) ⟩
       Tᶠ M (uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ))
    ∘ᵐ strᵀ M
  ≡⟨ ∘ᵐ-congˡ (cong (Tᶠ M) (cong uncurryᵐ (∘ᵐ-identityˡ _))) ⟩
       Tᶠ M (uncurryᵐ (curryᵐ idᵐ))
    ∘ᵐ strᵀ M
  ≡⟨ ∘ᵐ-congˡ (cong (Tᶠ M) (curryᵐ-uncurryᵐ-iso _)) ⟩
       Tᶠ M idᵐ
    ∘ᵐ strᵀ M
  ≡⟨ ∘ᵐ-congˡ (T-idᵐ M) ⟩
       idᵐ
    ∘ᵐ strᵀ M
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    strᵀ M
  ∎


ET-to-T-to-ET : ∀ {A B τ}
             → (M : EMonad)
             → enrᴱᵀ (T-to-ET (ET-to-T M)) {A} {B} {τ}
             ≡ enrᴱᵀ M

ET-to-T-to-ET {A} {B} {τ} M =
  begin
    enrᴱᵀ (T-to-ET (ET-to-T M)) {A} {B} {τ}
  ≡⟨⟩
    curryᵐ (   ETᶠ M (uncurryᵐ idᵐ)
            ∘ᵐ uncurryᵐ (enrᴱᵀ M)
            ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
  ≡⟨ cong curryᵐ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-map⇒ᵐ _ _)))) ⟩
    curryᵐ (   uncurryᵐ (   map⇒ᵐ idᵐ (ETᶠ M (uncurryᵐ idᵐ))
                         ∘ᵐ enrᴱᵀ M)
            ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congˡ (cong₂ map⇒ᵐ (sym (ET-idᵐ M)) refl)))) ⟩
    curryᵐ (   uncurryᵐ (   map⇒ᵐ (ETᶠ M idᵐ) (ETᶠ M (uncurryᵐ idᵐ))
                         ∘ᵐ enrᴱᵀ M)
            ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congˡ (cong uncurryᵐ (enrᴱᵀ-nat M _ _))) ⟩
    curryᵐ (   uncurryᵐ (   enrᴱᵀ M
                         ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ idᵐ)))
            ∘ᵐ mapˣᵐ ([ τ ]ᶠ (curryᵐ idᵐ)) idᵐ)
  ≡⟨ cong curryᵐ (trans (sym (uncurryᵐ-nat _ _)) (cong uncurryᵐ (∘ᵐ-assoc _ _ _))) ⟩
    curryᵐ (uncurryᵐ (   enrᴱᵀ M
                      ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ idᵐ))
                      ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)))
  ≡⟨ uncurryᵐ-curryᵐ-iso _ ⟩
       enrᴱᵀ M
    ∘ᵐ [ τ ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ idᵐ))
    ∘ᵐ [ τ ]ᶠ (curryᵐ idᵐ)
  ≡⟨ ∘ᵐ-congʳ (sym ([]-∘ᵐ _ _)) ⟩
       enrᴱᵀ M
    ∘ᵐ [ τ ]ᶠ (   map⇒ᵐ idᵐ (uncurryᵐ idᵐ)
               ∘ᵐ curryᵐ idᵐ)
  ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (sym (curryᵐ-map⇒ᵐ _ _))) ⟩
       enrᴱᵀ M
    ∘ᵐ [ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ ∘ᵐ idᵐ))
  ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (cong curryᵐ (∘ᵐ-identityʳ _))) ⟩
       enrᴱᵀ M
    ∘ᵐ [ τ ]ᶠ (curryᵐ (uncurryᵐ idᵐ))
  ≡⟨ ∘ᵐ-congʳ (cong [ τ ]ᶠ (uncurryᵐ-curryᵐ-iso _)) ⟩
       enrᴱᵀ M
    ∘ᵐ [ τ ]ᶠ idᵐ
  ≡⟨ ∘ᵐ-congʳ []-idᵐ ⟩
       enrᴱᵀ M
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    enrᴱᵀ M
  ∎
