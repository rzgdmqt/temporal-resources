------------------------------------------------------------------------
-- Derived properties for the category for the models of the language --
------------------------------------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.Category.Derived (Cat : Category) where

open Category Cat

-- BINARY PRODUCTS

⟨⟩ᵗ-∘ᵗ : ∀ {A B C D} → (f : A →ᵗ B) → (g : B →ᵗ C) → (h : B →ᵗ D)
       → ⟨ g ∘ᵗ f , h ∘ᵗ f ⟩ᵗ ≡ᵗ ⟨ g , h ⟩ᵗ ∘ᵗ f
⟨⟩ᵗ-∘ᵗ f g h = 
  begin
    ⟨ g ∘ᵗ f , h ∘ᵗ f ⟩ᵗ
  ≡⟨ ≡ᵗ-sym
       (⟨⟩ᵗ-unique
         (g ∘ᵗ f) (h ∘ᵗ f) (⟨ g , h ⟩ᵗ ∘ᵗ f)
         (begin
            fstᵗ ∘ᵗ ⟨ g , h ⟩ᵗ ∘ᵗ f
          ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc fstᵗ ⟨ g , h ⟩ᵗ f) ⟩
            (fstᵗ ∘ᵗ ⟨ g , h ⟩ᵗ) ∘ᵗ f
          ≡⟨ ∘ᵗ-congˡ (⟨⟩ᵗ-fstᵗ g h) ⟩
            g ∘ᵗ f
          ∎)
         (begin
            sndᵗ ∘ᵗ ⟨ g , h ⟩ᵗ ∘ᵗ f
          ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc sndᵗ ⟨ g , h ⟩ᵗ f) ⟩
            (sndᵗ ∘ᵗ ⟨ g , h ⟩ᵗ) ∘ᵗ f
          ≡⟨ ∘ᵗ-congˡ (⟨⟩ᵗ-sndᵗ g h) ⟩
            h ∘ᵗ f
          ∎))
   ⟩
    ⟨ g , h ⟩ᵗ ∘ᵗ f
  ∎

mapˣᵗ-×ᵗ-assoc : ∀ {A B C A' B' C'} → (f : A →ᵗ A') (g : B →ᵗ B') (h : C →ᵗ C')
               → mapˣᵗ (mapˣᵗ f g) h ∘ᵗ ×ᵗ-assoc ≡ᵗ ×ᵗ-assoc ∘ᵗ mapˣᵗ f (mapˣᵗ g h)
mapˣᵗ-×ᵗ-assoc f g h = 
  begin
    mapˣᵗ (mapˣᵗ f g) h ∘ᵗ ×ᵗ-assoc
  ≡⟨⟩
       ⟨ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ
    ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
  ≡⟨ ≡ᵗ-sym (⟨⟩ᵗ-∘ᵗ _ _ _) ⟩
    ⟨    (⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ fstᵗ)
      ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ ,
         (h ∘ᵗ sndᵗ)
      ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ ⟩ᵗ
  ≡⟨ ≡ᵗ-cong₂ ⟨_,_⟩ᵗ
      (begin
           (⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ fstᵗ)
        ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
           ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ
        ∘ᵗ fstᵗ
        ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _) ⟩
           ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ
        ∘ᵗ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ≡⟨ ≡ᵗ-sym (⟨⟩ᵗ-∘ᵗ _ _ _) ⟩
        ⟨ (f ∘ᵗ fstᵗ) ∘ᵗ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ ,
          (g ∘ᵗ sndᵗ) ∘ᵗ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ ⟩ᵗ
      ≡⟨ ≡ᵗ-cong₂ ⟨_,_⟩ᵗ
          (≡ᵗ-trans
            (∘ᵗ-assoc _ _ _)
            (≡ᵗ-trans
              (∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _))
              (≡ᵗ-sym (⟨⟩ᵗ-fstᵗ _ _))))
          (≡ᵗ-trans
            (∘ᵗ-assoc _ _ _)
            (≡ᵗ-trans
              (∘ᵗ-congʳ (⟨⟩ᵗ-sndᵗ _ _))
              (≡ᵗ-sym
                (≡ᵗ-trans
                  (∘ᵗ-assoc _ _ _)
                  (≡ᵗ-trans
                    (∘ᵗ-congʳ (⟨⟩ᵗ-sndᵗ _ _))
                    (≡ᵗ-trans
                      (≡ᵗ-sym (∘ᵗ-assoc _ _ _))
                      (≡ᵗ-trans
                        (∘ᵗ-congˡ (⟨⟩ᵗ-fstᵗ _ _))
                        (∘ᵗ-assoc _ _ _)))))))) ⟩
        ⟨    fstᵗ
          ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ ,
             (fstᵗ ∘ᵗ sndᵗ)
          ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ ⟩ᵗ
      ≡⟨ ⟨⟩ᵗ-∘ᵗ _ _ _ ⟩
           ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ
        ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ∎)
      (begin
           (h ∘ᵗ sndᵗ)
        ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
           h
        ∘ᵗ sndᵗ
        ∘ᵗ ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-sndᵗ _ _) ⟩
           h
        ∘ᵗ sndᵗ ∘ᵗ sndᵗ
      ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
           (h ∘ᵗ sndᵗ)
        ∘ᵗ sndᵗ
      ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (⟨⟩ᵗ-sndᵗ _ _)) ⟩
           (   sndᵗ
            ∘ᵗ ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ)
        ∘ᵗ sndᵗ
      ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
           sndᵗ
        ∘ᵗ ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ
      ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩ᵗ-sndᵗ _ _)) ⟩
           sndᵗ
        ∘ᵗ sndᵗ
        ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
           (sndᵗ ∘ᵗ sndᵗ)
        ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ∎) ⟩
    ⟨    ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ
      ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ ,
         (sndᵗ ∘ᵗ sndᵗ)
      ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ ⟩ᵗ
  ≡⟨ ⟨⟩ᵗ-∘ᵗ _ _ _ ⟩
       ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
    ∘ᵗ ⟨ f ∘ᵗ fstᵗ , ⟨ g ∘ᵗ fstᵗ , h ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ sndᵗ ⟩ᵗ
  ≡⟨⟩
    ×ᵗ-assoc ∘ᵗ mapˣᵗ f (mapˣᵗ g h)
  ∎

mapˣᵗ-∘ᵗ : ∀ {A A' A'' B B' B''} → (f : A →ᵗ A') (g : B →ᵗ B') (h : A' →ᵗ A'') (i : B' →ᵗ B'')
         → mapˣᵗ (h ∘ᵗ f) (i ∘ᵗ g) ≡ᵗ mapˣᵗ h i ∘ᵗ mapˣᵗ f g
mapˣᵗ-∘ᵗ f g h i = 
  begin
    mapˣᵗ (h ∘ᵗ f) (i ∘ᵗ g)
  ≡⟨⟩
    ⟨ (h ∘ᵗ f) ∘ᵗ fstᵗ , (i ∘ᵗ g) ∘ᵗ sndᵗ ⟩ᵗ
  ≡⟨ ≡ᵗ-cong₂ ⟨_,_⟩ᵗ
      (≡ᵗ-sym
        (≡ᵗ-trans
          (∘ᵗ-assoc _ _ _)
          (≡ᵗ-trans
            (∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _))
            (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))))
      (≡ᵗ-sym
        (≡ᵗ-trans
          (∘ᵗ-assoc _ _ _)
          (≡ᵗ-trans
            (∘ᵗ-congʳ (⟨⟩ᵗ-sndᵗ _ _))
            (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))) ⟩
    ⟨ (h ∘ᵗ fstᵗ) ∘ᵗ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ ,
      (i ∘ᵗ sndᵗ) ∘ᵗ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ ⟩ᵗ
  ≡⟨ ⟨⟩ᵗ-∘ᵗ _ _ _ ⟩
    ⟨ h ∘ᵗ fstᵗ , i ∘ᵗ sndᵗ ⟩ᵗ ∘ᵗ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ
  ≡⟨⟩
    mapˣᵗ h i ∘ᵗ mapˣᵗ f g
  ∎
