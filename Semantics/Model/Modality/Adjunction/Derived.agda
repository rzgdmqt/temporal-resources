---------------------------------------------------------------
-- Adjunction between the `[ t ] A` and `Γ ⟨ t ⟩` modalities --
---------------------------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction

module Semantics.Model.Modality.Adjunction.Derived (Cat : Category)
                                                   (Fut : Future Cat)
                                                   (Pas : Past Cat)
                                                   (Adj : Adjunction Cat Fut Pas) where

open import Util.Equality
open import Util.Time

open Category Cat
open Future Fut
open Past Pas
open Adjunction Adj

open import Semantics.Model.Category.Derived Cat

-- [_]ᵒ is monoidal (with respect to ×ᵐ)
 
[]-monoidal : ∀ {A B τ}
            → [ τ ]ᵒ A ×ᵐ [ τ ]ᵒ B →ᵐ [ τ ]ᵒ (A ×ᵐ B)

[]-monoidal {A} {B} {τ} =
     [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ ,
              ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
  ∘ᵐ η⊣ {τ = τ}

-- monoidality witness is natural

[]-monoidal-nat : ∀ {A B C D τ}
                → (f : A →ᵐ C)
                → (g : B →ᵐ D)
                → [ τ ]ᶠ (mapˣᵐ f g) ∘ᵐ []-monoidal
                ≡ []-monoidal ∘ᵐ mapˣᵐ ([ τ ]ᶠ f) ([ τ ]ᶠ g)

[]-monoidal-nat {A} {B} {C} {D} {τ} f g =
  begin
       [ τ ]ᶠ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
      (trans (sym ([]-∘ᵐ _ _)) (trans
        (cong [ τ ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (trans
          (cong₂ ⟨_,_⟩ᵐ
            (begin
                 (f ∘ᵐ fstᵐ)
              ∘ᵐ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                 f
              ∘ᵐ fstᵐ
              ∘ᵐ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
                 f
              ∘ᵐ ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ
            ≡⟨ trans (sym (∘ᵐ-assoc _ _ _))
                (trans (∘ᵐ-congˡ (ε⊣-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f)
              ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ
            ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _)) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f ∘ᵐ fstᵐ)
            ≡⟨ ∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (sym (⟨⟩ᵐ-fstᵐ _ _))) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ (   fstᵐ
                         ∘ᵐ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ)
            ≡⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ
              ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ
            ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                 (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ)
              ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ
            ∎)
            (begin
                 (g ∘ᵐ sndᵐ)
              ∘ᵐ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                 g
              ∘ᵐ sndᵐ
              ∘ᵐ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
            ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ⟩
                 g
              ∘ᵐ ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
            ≡⟨ trans (sym (∘ᵐ-assoc _ _ _))
                (trans (∘ᵐ-congˡ (ε⊣-nat _)) (∘ᵐ-assoc _ _ _)) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ g)
              ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
            ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _)) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ g ∘ᵐ sndᵐ)
            ≡⟨ ∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ (   sndᵐ
                         ∘ᵐ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ)
            ≡⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩
                 ε⊣
              ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
              ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ
            ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                 (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
              ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ
            ∎))
          (⟨⟩ᵐ-∘ᵐ _ _ _)))) ([]-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _)) ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (η⊣-nat _) ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ η⊣
    ∘ᵐ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
        ∘ᵐ η⊣)
    ∘ᵐ ⟨ [ τ ]ᶠ f ∘ᵐ fstᵐ , [ τ ]ᶠ g ∘ᵐ sndᵐ ⟩ᵐ
  ∎

-- monoidality witness's interaction with projections

[]-monoidal-fstᵐ : ∀ {A B τ}
                 → [ τ ]ᶠ fstᵐ ∘ᵐ []-monoidal {A} {B} ≡ fstᵐ

[]-monoidal-fstᵐ {A} {B} {τ} = 
  begin
       [ τ ]ᶠ fstᵐ
    ∘ᵐ [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))) ⟩
       [ τ ]ᶠ (   fstᵐ
               ∘ᵐ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (⟨⟩ᵐ-fstᵐ _ _)) ⟩
       [ τ ]ᶠ (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ)
    ∘ᵐ η⊣
  ≡⟨ trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _) ⟩
       [ τ ]ᶠ ε⊣
    ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ fstᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (η⊣-nat _) ⟩
       [ τ ]ᶠ ε⊣
    ∘ᵐ η⊣
    ∘ᵐ fstᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ Gε⊣∘η⊣≡id) ⟩
       idᵐ
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    fstᵐ
  ∎

[]-monoidal-sndᵐ : ∀ {A B τ}
                 → [ τ ]ᶠ sndᵐ ∘ᵐ []-monoidal {A} {B} ≡ sndᵐ

[]-monoidal-sndᵐ {A} {B} {τ} = 
  begin
       [ τ ]ᶠ sndᵐ
    ∘ᵐ [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))) ⟩
       [ τ ]ᶠ (   sndᵐ
               ∘ᵐ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (⟨⟩ᵐ-sndᵐ _ _)) ⟩
       [ τ ]ᶠ (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
    ∘ᵐ η⊣
  ≡⟨ trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _) ⟩
       [ τ ]ᶠ ε⊣
    ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ sndᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ (η⊣-nat _) ⟩
       [ τ ]ᶠ ε⊣
    ∘ᵐ η⊣
    ∘ᵐ sndᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ Gε⊣∘η⊣≡id) ⟩
       idᵐ
    ∘ᵐ sndᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    sndᵐ
  ∎

-- monoidality witness's interaction with pairing

[]-monoidal-⟨⟩ᵐ : ∀ {A B C τ}
                → (f : A →ᵐ B)
                → (g : A →ᵐ C)
                → []-monoidal ∘ᵐ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ
                ≡ [ τ ]ᶠ ⟨ f , g ⟩ᵐ

[]-monoidal-⟨⟩ᵐ {A} {B} {C} {τ} f g = 
  begin
       (   [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
        ∘ᵐ η⊣)
    ∘ᵐ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ η⊣
    ∘ᵐ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (η⊣-nat _)) ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
    ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym ([]-∘ᵐ _ _))) ⟩
       [ τ ]ᶠ (   ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ⟩ᵐ
               ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ)
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))) ⟩
       [ τ ]ᶠ ⟨ (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ  ,
                (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ) ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _))) ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ  ,
                ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ ∘ᵐ ⟨ τ ⟩ᶠ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ
      (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))))) ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ (fstᵐ ∘ᵐ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ)  ,
                ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ (sndᵐ ∘ᵐ ⟨ [ τ ]ᶠ f , [ τ ]ᶠ g ⟩ᵐ) ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (cong₂ ⟨_,_⟩ᵐ
      (∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (⟨⟩ᵐ-fstᵐ _ _)))
      (∘ᵐ-congʳ (cong ⟨ τ ⟩ᶠ (⟨⟩ᵐ-sndᵐ _ _))))) ⟩
       [ τ ]ᶠ ⟨ ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ f)  ,
                ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ([ τ ]ᶠ g) ⟩ᵐ
    ∘ᵐ η⊣
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym ([]-∘ᵐ _ _))
      (cong [ τ ]ᶠ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
        (cong₂ ⟨_,_⟩ᵐ (ε⊣-nat _) (ε⊣-nat _))))))) ⟩
       [ τ ]ᶠ ⟨ f , g ⟩ᵐ
    ∘ᵐ [ τ ]ᶠ ε⊣
    ∘ᵐ η⊣
  ≡⟨ ∘ᵐ-congʳ Gε⊣∘η⊣≡id ⟩
       [ τ ]ᶠ ⟨ f , g ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    [ τ ]ᶠ ⟨ f , g ⟩ᵐ
  ∎
