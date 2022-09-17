-------------------------------------------------------
-- Category structure for the models of the language --
-------------------------------------------------------

module Semantics.Model.Category where

open import Util.Equality

record Category : Set₂ where

  -- OBJECTS AND MORPHISMS
  
  field
    Obj : Set₁
    
    _→ᵐ_ : (A B : Obj) → Set₀

  infix 20 _→ᵐ_

  -- IDENTITIES AND COMPOSITION
  
  field
    idᵐ : ∀ {A} → A →ᵐ A
    _∘ᵐ_ : ∀ {A B C} → B →ᵐ C → A →ᵐ B → A →ᵐ C

    ∘ᵐ-identityˡ : ∀ {A B} → (f : A →ᵐ B) → idᵐ ∘ᵐ f ≡ f
    ∘ᵐ-identityʳ : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ idᵐ ≡ f   
    ∘ᵐ-assoc : ∀ {A B C D} → (h : C →ᵐ D) → (g : B →ᵐ C) → (f : A →ᵐ B) → (h ∘ᵐ g) ∘ᵐ f ≡ h ∘ᵐ (g ∘ᵐ f)
    
  infixr 9 _∘ᵐ_

  -- TERMINAL OBJECT

  field
    𝟙ᵐ : Obj

    terminalᵐ : ∀ {A} → A →ᵐ 𝟙ᵐ
    terminalᵐ-unique : ∀ {A} {f : A →ᵐ 𝟙ᵐ} → f ≡ terminalᵐ

  -- INITIAL OBJECT
  
  field
    𝟘ᵐ : Obj

    initialᵐ : ∀ {A} → 𝟘ᵐ →ᵐ A
    initialᵐ-unique : ∀ {A} {f : 𝟘ᵐ →ᵐ A} → f ≡ initialᵐ

  -- BINARY PRODUCTS

  field
    _×ᵐ_ : Obj → Obj → Obj

    fstᵐ : ∀ {A B} → A ×ᵐ B →ᵐ A
    sndᵐ : ∀ {A B} → A ×ᵐ B →ᵐ B
    ⟨_,_⟩ᵐ : ∀ {A B C} → A →ᵐ B → A →ᵐ C → A →ᵐ B ×ᵐ C

    ⟨⟩ᵐ-fstᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → fstᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≡ f
    ⟨⟩ᵐ-sndᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → sndᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≡ g
    ⟨⟩ᵐ-unique : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → (h : A →ᵐ B ×ᵐ C) → fstᵐ ∘ᵐ h ≡ f → sndᵐ ∘ᵐ h ≡ g → h ≡ ⟨ f , g ⟩ᵐ

  mapˣᵐ : ∀ {A B C D} → A →ᵐ C → B →ᵐ D → A ×ᵐ B →ᵐ C ×ᵐ D
  mapˣᵐ f g = ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
   
  ×ᵐ-assoc : ∀ {A B C} → A ×ᵐ (B ×ᵐ C) →ᵐ (A ×ᵐ B) ×ᵐ C
  ×ᵐ-assoc = ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
   
  ×ᵐ-assoc⁻¹ : ∀ {A B C} → (A ×ᵐ B) ×ᵐ C →ᵐ A ×ᵐ (B ×ᵐ C)
  ×ᵐ-assoc⁻¹ = ⟨ fstᵐ ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
   
  ×ᵐ-swap : ∀ {A B} → A ×ᵐ B →ᵐ B ×ᵐ A
  ×ᵐ-swap = ⟨ sndᵐ , fstᵐ ⟩ᵐ

  infixr 23 _×ᵐ_

  -- SET-INDEXED PRODUCTS

  field
    Π : (I : Set) → (I → Obj) → Obj
    
    projᵐ : ∀ {I A} → (i : I) → Π I A →ᵐ A i
    ⟨_⟩ᵢᵐ : ∀ {I A B} → ((i : I) → A →ᵐ B i) → A →ᵐ Π I B

    ⟨⟩ᵢᵐ-projᵐ : ∀ {I} {A} {B : I → Obj} → (f : ((i : I) → A →ᵐ B i)) → (i : I) → projᵐ i ∘ᵐ ⟨ f ⟩ᵢᵐ ≡ f i
    ⟨⟩ᵢᵐ-unique : ∀ {I} {A} {B : I → Obj}
                → (f : (i : I) → A →ᵐ B i)
                → (g : A →ᵐ Π I B)
                → ((i : I) → (projᵐ i ∘ᵐ g) ≡ f i)
                → g ≡ ⟨ f ⟩ᵢᵐ

  -- EXPONENTIALS

  field
    _⇒ᵐ_ : Obj → Obj → Obj

    appᵐ : ∀ {A B} → (A ⇒ᵐ B) ×ᵐ A →ᵐ B
    map⇒ᵐ : ∀ {A B C D} → (A →ᵐ B) → (C →ᵐ D) → B ⇒ᵐ C →ᵐ A ⇒ᵐ D
    curryᵐ : ∀ {A B C} → A ×ᵐ B →ᵐ C → A →ᵐ B ⇒ᵐ C
    uncurryᵐ : ∀ {A B C} → A →ᵐ B ⇒ᵐ C → A ×ᵐ B →ᵐ C

    map⇒ᵐ-identity : ∀ {A B} → map⇒ᵐ {A} {A} {B} {B} idᵐ idᵐ ≡ idᵐ
    
    curryᵐ-mapˣᵐ : ∀ {A B C D E} → (f : C ×ᵐ D →ᵐ E) → (g : A →ᵐ C) → (h : B →ᵐ D)
                 → curryᵐ (f ∘ᵐ mapˣᵐ g h) ≡ map⇒ᵐ h idᵐ ∘ᵐ curryᵐ f ∘ᵐ g
    uncurryᵐ-mapˣᵐʳ : ∀ {A B C D} → (f : A →ᵐ B) → (g : B →ᵐ C ⇒ᵐ D) → uncurryᵐ (g ∘ᵐ f) ≡ uncurryᵐ g ∘ᵐ mapˣᵐ f idᵐ

  infixr 22 _⇒ᵐ_
