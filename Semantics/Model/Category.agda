-------------------------------------------------------
-- Category structure for the models of the language --
-------------------------------------------------------

module Semantics.Model.Category where

open import Util.Equality

record Category : Set₂ where

  -- OBJECTS AND MORPHISMS
  
  field
    TSet : Set₁
    
    _→ᵗ_ : (A B : TSet) → Set₀

  infix 20 _→ᵗ_

  -- EQUALITY ON MORPHISMS ()

  field
    _≡ᵗ_ : {A B : TSet} (f g : A →ᵗ B) → Set

    ≡ᵗ-refl : ∀ {A B} {f : A →ᵗ B} → f ≡ᵗ f
    ≡ᵗ-sym : ∀ {A B} {f g : A →ᵗ B} → f ≡ᵗ g → g ≡ᵗ f
    ≡ᵗ-trans : ∀ {A B} {f g h : A →ᵗ B} → f ≡ᵗ g → g ≡ᵗ h → f ≡ᵗ h

    begin_ : ∀ {A B} {f g : A →ᵗ B} → f ≡ᵗ g → f ≡ᵗ g
     
    _≡⟨⟩_ : ∀ {A B} (f {g} : A →ᵗ B) → f ≡ᵗ g → f ≡ᵗ g
     
    step-≡ : ∀ {A B} (f {g h} : A →ᵗ B) → g ≡ᵗ h → f ≡ᵗ g → f ≡ᵗ h
     
    _∎ : ∀ {A B} (f : A →ᵗ B) → f ≡ᵗ f

    ≡ᵗ-≡ : ∀ {A B} → {f g : A →ᵗ B} → f ≡ᵗ g → f ≡ g
    ≡-≡ᵗ : ∀ {A B} → {f g : A →ᵗ B} → f ≡ g → f ≡ᵗ g

    ≡ᵗ-cong : ∀ {A B C D} (f : (A →ᵗ B) → (C →ᵗ D)) {x y : A →ᵗ B}
            → x ≡ᵗ y → f x ≡ᵗ f y
    ≡ᵗ-cong₂ : ∀ {A B C D E F} (f : (A →ᵗ B) → (C →ᵗ D) → (E →ᵗ F))
             → {x y : A →ᵗ B} {z w : C →ᵗ D}
             → x ≡ᵗ y → z ≡ᵗ w → f x z ≡ᵗ f y w

  infix  5 _≡ᵗ_
  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡
  infix  1 begin_

  syntax step-≡ f g≡h f≡g = f ≡⟨ f≡g ⟩ g≡h

  -- iDENTITIES AND COMPOSITION
  
  field
    idᵗ : ∀ {A} → A →ᵗ A
    _∘ᵗ_ : ∀ {A B C} → B →ᵗ C → A →ᵗ B → A →ᵗ C

    ∘ᵗ-identityˡ : ∀ {A B} → (f : A →ᵗ B) → idᵗ ∘ᵗ f ≡ᵗ f
    ∘ᵗ-identityʳ : ∀ {A B} → (f : A →ᵗ B) → f ∘ᵗ idᵗ ≡ᵗ f   
    ∘ᵗ-assoc : ∀ {A B C D} → (h : C →ᵗ D) → (g : B →ᵗ C) → (f : A →ᵗ B) → (h ∘ᵗ g) ∘ᵗ f ≡ᵗ h ∘ᵗ (g ∘ᵗ f)
    ∘ᵗ-congˡ : ∀ {A B C} → {f : A →ᵗ B} → {g h : B →ᵗ C} → g ≡ᵗ h → g ∘ᵗ f ≡ᵗ h ∘ᵗ f
    ∘ᵗ-congʳ : ∀ {A B C} → {f g : A →ᵗ B} → {h : B →ᵗ C} → f ≡ᵗ g → h ∘ᵗ f ≡ᵗ h ∘ᵗ g

  infixr 9 _∘ᵗ_

  -- TERMINAL OBJECT

  field
    𝟙ᵗ : TSet

    terminalᵗ : ∀ {A} → A →ᵗ 𝟙ᵗ
    terminalᵗ-unique : ∀ {A} {f : A →ᵗ 𝟙ᵗ} → f ≡ᵗ terminalᵗ

  -- INITIAL OBJECT
  
  field
    𝟘ᵗ : TSet

    initialᵗ : ∀ {A} → 𝟘ᵗ →ᵗ A
    initialᵗ-unique : ∀ {A} {f : 𝟘ᵗ →ᵗ A} → f ≡ᵗ initialᵗ

  -- BINARY PRODUCTS

  field
    _×ᵗ_ : TSet → TSet → TSet

    fstᵗ : ∀ {A B} → A ×ᵗ B →ᵗ A
    sndᵗ : ∀ {A B} → A ×ᵗ B →ᵗ B
    ⟨_,_⟩ᵗ : ∀ {A B C} → A →ᵗ B → A →ᵗ C → A →ᵗ B ×ᵗ C

    ⟨⟩ᵗ-fstᵗ : ∀ {A B C} → (f : A →ᵗ B) → (g : A →ᵗ C) → fstᵗ ∘ᵗ ⟨ f , g ⟩ᵗ ≡ᵗ f
    ⟨⟩ᵗ-sndᵗ : ∀ {A B C} → (f : A →ᵗ B) → (g : A →ᵗ C) → sndᵗ ∘ᵗ ⟨ f , g ⟩ᵗ ≡ᵗ g
    ⟨⟩ᵗ-unique : ∀ {A B C} → (f : A →ᵗ B) → (g : A →ᵗ C) → (h : A →ᵗ B ×ᵗ C) → fstᵗ ∘ᵗ h ≡ᵗ f → sndᵗ ∘ᵗ h ≡ᵗ g → h ≡ᵗ ⟨ f , g ⟩ᵗ

  mapˣᵗ : ∀ {A B C D} → A →ᵗ C → B →ᵗ D → A ×ᵗ B →ᵗ C ×ᵗ D
  mapˣᵗ f g = ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ
   
  ×ᵗ-assoc : ∀ {A B C} → A ×ᵗ (B ×ᵗ C) →ᵗ (A ×ᵗ B) ×ᵗ C
  ×ᵗ-assoc = ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
   
  ×ᵗ-assoc⁻¹ : ∀ {A B C} → (A ×ᵗ B) ×ᵗ C →ᵗ A ×ᵗ (B ×ᵗ C)
  ×ᵗ-assoc⁻¹ = ⟨ fstᵗ ∘ᵗ fstᵗ , ⟨ sndᵗ ∘ᵗ fstᵗ , sndᵗ ⟩ᵗ ⟩ᵗ
   
  ×ᵗ-swap : ∀ {A B} → A ×ᵗ B →ᵗ B ×ᵗ A
  ×ᵗ-swap = ⟨ sndᵗ , fstᵗ ⟩ᵗ

  infixr 23 _×ᵗ_

  -- SET-INDEXED PRODUCTS

  field
    Π : (I : Set) → (I → TSet) → TSet
    
    projᵗ : ∀ {I A} → (i : I) → Π I A →ᵗ A i
    ⟨_⟩ᵢᵗ : ∀ {I A B} → ((i : I) → A →ᵗ B i) → A →ᵗ Π I B

  mapⁱˣᵗ : ∀ {I A B} → ((i : I) → A i →ᵗ B i) → Π I A →ᵗ Π I B
  mapⁱˣᵗ fs = ⟨ (λ i → fs i ∘ᵗ projᵗ i) ⟩ᵢᵗ

  field
    mapⁱˣᵗ-identity : ∀ {I A} → mapⁱˣᵗ {I} {A} {A} (λ i → idᵗ) ≡ᵗ idᵗ
    mapⁱˣᵗ-∘ᵗ : ∀ {I} {A B C : I → TSet} → (f : ((i : I) → A i →ᵗ B i)) → (g : ((i : I) → B i →ᵗ C i))
              → mapⁱˣᵗ (λ i → g i ∘ᵗ f i) ≡ᵗ mapⁱˣᵗ g ∘ᵗ mapⁱˣᵗ f

    ⟨⟩ᵢᵗ-projᵗ : ∀ {I} {A} {B : I → TSet} → (f : ((i : I) → A →ᵗ B i)) → (i : I) → projᵗ i ∘ᵗ ⟨ f ⟩ᵢᵗ ≡ᵗ f i
    ⟨⟩ᵢᵗ-∘ᵗ : ∀ {I} {A B} {C : I → TSet} → (f : A →ᵗ B) → (g : ((i : I) → B →ᵗ C i)) → ⟨ (λ i → g i ∘ᵗ f) ⟩ᵢᵗ ≡ᵗ ⟨ g ⟩ᵢᵗ ∘ᵗ f

  -- EXPONENTIALS

  field
    _⇒ᵗ_ : TSet → TSet → TSet

    appᵗ : ∀ {A B} → (A ⇒ᵗ B) ×ᵗ A →ᵗ B
    map⇒ᵗ : ∀ {A B C D} → (A →ᵗ B) → (C →ᵗ D) → B ⇒ᵗ C →ᵗ A ⇒ᵗ D
    curryᵗ : ∀ {A B C} → A ×ᵗ B →ᵗ C → A →ᵗ B ⇒ᵗ C
    uncurryᵗ : ∀ {A B C} → A →ᵗ B ⇒ᵗ C → A ×ᵗ B →ᵗ C

    map⇒ᵗ-identity : ∀ {A B} → map⇒ᵗ {A} {A} {B} {B} idᵗ idᵗ ≡ᵗ idᵗ
    
    curryᵗ-mapˣᵗ : ∀ {A B C D E} → (f : C ×ᵗ D →ᵗ E) → (g : A →ᵗ C) → (h : B →ᵗ D)
                 → curryᵗ (f ∘ᵗ mapˣᵗ g h) ≡ᵗ map⇒ᵗ h idᵗ ∘ᵗ curryᵗ f ∘ᵗ g
    uncurryᵗ-mapʳ : ∀ {A B C D} → (f : A →ᵗ B) → (g : B →ᵗ C ⇒ᵗ D) → uncurryᵗ (g ∘ᵗ f) ≡ᵗ uncurryᵗ g ∘ᵗ mapˣᵗ f idᵗ

  infixr 22 _⇒ᵗ_
