------------------------------------------------------------------------
-- Derived properties for the category for the models of the language --
------------------------------------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.Category.Derived (Cat : Category) where

open import Util.Equality

open Category Cat

-- CONGRUENCE OF MORPHISM COMPOSITION

∘ᵐ-congˡ : ∀ {A B C} → {f : A →ᵐ B} → {g h : B →ᵐ C} → g ≡ h → g ∘ᵐ f ≡ h ∘ᵐ f
∘ᵐ-congˡ {f = f} p =
  cong (_∘ᵐ f) p

∘ᵐ-congʳ : ∀ {A B C} → {f g : A →ᵐ B} → {h : B →ᵐ C} → f ≡ g → h ∘ᵐ f ≡ h ∘ᵐ g
∘ᵐ-congʳ {h = h} p =
  cong (h ∘ᵐ_) p

-- BINARY PRODUCTS

⟨⟩ᵐ-∘ᵐ : ∀ {A B C D} → (f : A →ᵐ B) → (g : B →ᵐ C) → (h : B →ᵐ D)
       → ⟨ g ∘ᵐ f , h ∘ᵐ f ⟩ᵐ ≡ ⟨ g , h ⟩ᵐ ∘ᵐ f
⟨⟩ᵐ-∘ᵐ f g h = 
  begin
    ⟨ g ∘ᵐ f , h ∘ᵐ f ⟩ᵐ
  ≡⟨ sym
       (⟨⟩ᵐ-unique
         (g ∘ᵐ f) (h ∘ᵐ f) (⟨ g , h ⟩ᵐ ∘ᵐ f)
         (begin
            fstᵐ ∘ᵐ ⟨ g , h ⟩ᵐ ∘ᵐ f
          ≡⟨ sym (∘ᵐ-assoc fstᵐ ⟨ g , h ⟩ᵐ f) ⟩
            (fstᵐ ∘ᵐ ⟨ g , h ⟩ᵐ) ∘ᵐ f
          ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ g h) ⟩
            g ∘ᵐ f
          ∎)
         (begin
            sndᵐ ∘ᵐ ⟨ g , h ⟩ᵐ ∘ᵐ f
          ≡⟨ sym (∘ᵐ-assoc sndᵐ ⟨ g , h ⟩ᵐ f) ⟩
            (sndᵐ ∘ᵐ ⟨ g , h ⟩ᵐ) ∘ᵐ f
          ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ g h) ⟩
            h ∘ᵐ f
          ∎))
   ⟩
    ⟨ g , h ⟩ᵐ ∘ᵐ f
  ∎

mapˣᵐ-×ᵐ-assoc : ∀ {A B C A' B' C'} → (f : A →ᵐ A') (g : B →ᵐ B') (h : C →ᵐ C')
               → mapˣᵐ (mapˣᵐ f g) h ∘ᵐ ×ᵐ-assoc ≡ ×ᵐ-assoc ∘ᵐ mapˣᵐ f (mapˣᵐ g h)
mapˣᵐ-×ᵐ-assoc f g h = 
  begin
    mapˣᵐ (mapˣᵐ f g) h ∘ᵐ ×ᵐ-assoc
  ≡⟨⟩
       ⟨ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
    ⟨    (⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ)
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
         (h ∘ᵐ sndᵐ)
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (begin
           (⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ)
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ fstᵐ
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
           ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
        ⟨ (f ∘ᵐ fstᵐ) ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
          (g ∘ᵐ sndᵐ) ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ cong₂ ⟨_,_⟩ᵐ
          (trans
            (∘ᵐ-assoc _ _ _)
            (trans
              (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              (sym (⟨⟩ᵐ-fstᵐ _ _))))
          (trans
            (∘ᵐ-assoc _ _ _)
            (trans
              (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
              (sym
                (trans
                  (∘ᵐ-assoc _ _ _)
                  (trans
                    (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                    (trans
                      (sym (∘ᵐ-assoc _ _ _))
                      (trans
                        (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                        (∘ᵐ-assoc _ _ _)))))))) ⟩
        ⟨    fstᵐ
          ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
             (fstᵐ ∘ᵐ sndᵐ)
          ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
           ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎)
      (begin
           (h ∘ᵐ sndᵐ)
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           h
        ∘ᵐ sndᵐ
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ⟩
           h
        ∘ᵐ sndᵐ ∘ᵐ sndᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (h ∘ᵐ sndᵐ)
        ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
           (   sndᵐ
            ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
        ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           sndᵐ
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
           sndᵐ
        ∘ᵐ sndᵐ
        ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (sndᵐ ∘ᵐ sndᵐ)
        ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎) ⟩
    ⟨    ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
         (sndᵐ ∘ᵐ sndᵐ)
      ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨⟩
    ×ᵐ-assoc ∘ᵐ mapˣᵐ f (mapˣᵐ g h)
  ∎

mapˣᵐ-∘ᵐ : ∀ {A A' A'' B B' B''} → (f : A →ᵐ A') (g : B →ᵐ B') (h : A' →ᵐ A'') (i : B' →ᵐ B'')
         → mapˣᵐ (h ∘ᵐ f) (i ∘ᵐ g) ≡ mapˣᵐ h i ∘ᵐ mapˣᵐ f g
mapˣᵐ-∘ᵐ f g h i = 
  begin
    mapˣᵐ (h ∘ᵐ f) (i ∘ᵐ g)
  ≡⟨⟩
    ⟨ (h ∘ᵐ f) ∘ᵐ fstᵐ , (i ∘ᵐ g) ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (sym
        (trans
          (∘ᵐ-assoc _ _ _)
          (trans
            (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
            (sym (∘ᵐ-assoc _ _ _)))))
      (sym
        (trans
          (∘ᵐ-assoc _ _ _)
          (trans
            (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
            (sym (∘ᵐ-assoc _ _ _))))) ⟩
    ⟨ (h ∘ᵐ fstᵐ) ∘ᵐ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ,
      (i ∘ᵐ sndᵐ) ∘ᵐ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
    ⟨ h ∘ᵐ fstᵐ , i ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨⟩
    mapˣᵐ h i ∘ᵐ mapˣᵐ f g
  ∎

-- SET-INDEXED PRODUCTS

⟨⟩ᵢᵐ-∘ᵐ : ∀ {I} {A B} {C : I → Obj}
        → (f : A →ᵐ B) → (g : ((i : I) → B →ᵐ C i))
        → ⟨ (λ i → g i ∘ᵐ f) ⟩ᵢᵐ ≡ ⟨ g ⟩ᵢᵐ ∘ᵐ f
⟨⟩ᵢᵐ-∘ᵐ f g = 
  begin
    ⟨ (λ i → g i ∘ᵐ f) ⟩ᵢᵐ
  ≡⟨ sym (⟨⟩ᵢᵐ-unique _ _ (λ i →
      begin
        projᵐ i ∘ᵐ ⟨ g ⟩ᵢᵐ ∘ᵐ f
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
        (projᵐ i ∘ᵐ ⟨ g ⟩ᵢᵐ) ∘ᵐ f
      ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵢᵐ-projᵐ _ _) ⟩
        g i ∘ᵐ f
      ∎)) ⟩
    ⟨ g ⟩ᵢᵐ ∘ᵐ f
  ∎

mapⁱˣᵐ : ∀ {I A B} → ((i : I) → A i →ᵐ B i) → Π I A →ᵐ Π I B
mapⁱˣᵐ fs = ⟨ (λ i → fs i ∘ᵐ projᵐ i) ⟩ᵢᵐ

mapⁱˣᵐ-identity : ∀ {I A} → mapⁱˣᵐ {I} {A} {A} (λ i → idᵐ) ≡ idᵐ
mapⁱˣᵐ-identity = 
  begin
    mapⁱˣᵐ (λ i → idᵐ)
  ≡⟨ sym (⟨⟩ᵢᵐ-unique _ _ (λ i → 
      begin
        projᵐ i ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        projᵐ i
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
        idᵐ ∘ᵐ projᵐ i
      ∎)) ⟩
    idᵐ
  ∎

mapⁱˣᵐ-∘ᵐ : ∀ {I} {A B C : I → Obj}
          → (f : ((i : I) → A i →ᵐ B i))
          → (g : ((i : I) → B i →ᵐ C i))
          → mapⁱˣᵐ (λ i → g i ∘ᵐ f i) ≡ mapⁱˣᵐ g ∘ᵐ mapⁱˣᵐ f
mapⁱˣᵐ-∘ᵐ f g = 
  begin
    mapⁱˣᵐ (λ i → g i ∘ᵐ f i)
  ≡⟨⟩
    ⟨ (λ i → (g i ∘ᵐ f i) ∘ᵐ projᵐ i) ⟩ᵢᵐ
  ≡⟨ sym (⟨⟩ᵢᵐ-unique _ _ (λ i →
      begin
           projᵐ i
        ∘ᵐ ⟨ (λ i₁ → g i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   projᵐ i
            ∘ᵐ ⟨ (λ i₁ → g i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ)
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵢᵐ-projᵐ _ _) ⟩
           (g i ∘ᵐ projᵐ i)
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           g i
        ∘ᵐ projᵐ i
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ _) ⟩
           g i
        ∘ᵐ f i
        ∘ᵐ projᵐ i
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
        (g i ∘ᵐ f i) ∘ᵐ projᵐ i
      ∎)) ⟩
    ⟨ (λ i → g i ∘ᵐ projᵐ i) ⟩ᵢᵐ ∘ᵐ ⟨ (λ i → f i ∘ᵐ projᵐ i) ⟩ᵢᵐ
  ≡⟨⟩
    mapⁱˣᵐ g ∘ᵐ mapⁱˣᵐ f
  ∎
