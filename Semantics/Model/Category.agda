-------------------------------------------------------
-- Category structure for the models of the language --
-------------------------------------------------------

module Semantics.Model.Category where

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

open import Util.Equality
open import Util.Time

record Model : Set₂ where

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

    ⟨⟩ᵗ-∘ᵗ : ∀ {A B C D} → (f : A →ᵗ B) → (g : B →ᵗ C) → (h : B →ᵗ D) → ⟨ g ∘ᵗ f , h ∘ᵗ f ⟩ᵗ ≡ᵗ ⟨ g , h ⟩ᵗ ∘ᵗ f

  mapˣᵗ : ∀ {A B C D} → A →ᵗ C → B →ᵗ D → A ×ᵗ B →ᵗ C ×ᵗ D
  mapˣᵗ f g = ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ
   
  ×ᵗ-assoc : ∀ {A B C} → A ×ᵗ (B ×ᵗ C) →ᵗ (A ×ᵗ B) ×ᵗ C
  ×ᵗ-assoc = ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
   
  ×ᵗ-assoc⁻¹ : ∀ {A B C} → (A ×ᵗ B) ×ᵗ C →ᵗ A ×ᵗ (B ×ᵗ C)
  ×ᵗ-assoc⁻¹ = ⟨ fstᵗ ∘ᵗ fstᵗ , ⟨ sndᵗ ∘ᵗ fstᵗ , sndᵗ ⟩ᵗ ⟩ᵗ
   
  ×ᵗ-swap : ∀ {A B} → A ×ᵗ B →ᵗ B ×ᵗ A
  ×ᵗ-swap = ⟨ sndᵗ , fstᵗ ⟩ᵗ

  field
    mapˣᵗ-×ᵗ-assoc : ∀ {A B C A' B' C'} → (f : A →ᵗ A') (g : B →ᵗ B') (h : C →ᵗ C')
                   → mapˣᵗ (mapˣᵗ f g) h ∘ᵗ ×ᵗ-assoc ≡ᵗ ×ᵗ-assoc ∘ᵗ mapˣᵗ f (mapˣᵗ g h)
    mapˣᵗ-∘ᵗ : ∀ {A A' A'' B B' B''} → (f : A →ᵗ A') (g : B →ᵗ B') (h : A' →ᵗ A'') (i : B' →ᵗ B'')
             → mapˣᵗ (h ∘ᵗ f) (i ∘ᵗ g) ≡ᵗ mapˣᵗ h i ∘ᵗ mapˣᵗ f g

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


  infixr 22 _⇒ᵗ_



{-


---- exponentials

abstract
  _⇒ᵗ_ : TSet → TSet → TSet
  A ⇒ᵗ B =
    tset
      (λ t → homᵒ t ×ᵗ A →ᵗ B)
      (λ p f → f ∘ᵗ mapˣᵗ (homᶠ p) idᵗ)
      (λ {t} f →
        ≡ᵗ-≡ (eqᵗ (λ { (p , x) →
          cong (λ q → map-carrier f (q , x)) (≤-irrelevant _ _) })))
      (λ p q f →
        ≡ᵗ-≡ (eqᵗ (λ { (r , x) →
          cong (λ s → map-carrier f (s , x)) (≤-irrelevant _ _) })))

infixr 22 _⇒ᵗ_

abstract
  appᵗ : ∀ {A B} → (A ⇒ᵗ B) ×ᵗ A →ᵗ B
  appᵗ {A} {B} =
    tset-map
      (λ { (f , x) → map-carrier f (≤-refl , x) })
      (λ { p (f , x) →
        trans
          (cong (λ q → map-carrier f (q , monotone A p x)) (≤-irrelevant _ _))
          (map-nat f p (≤-reflexive refl , x)) })
   
  map⇒ᵗ : ∀ {A B C D} → (A →ᵗ B) → (C →ᵗ D) → B ⇒ᵗ C →ᵗ A ⇒ᵗ D
  map⇒ᵗ f g =
    tset-map
      (λ h → g ∘ᵗ h ∘ᵗ mapˣᵗ idᵗ f)
      (λ p h → ≡ᵗ-≡ (eqᵗ (λ { (q , x) → refl })))

  curryᵗ : ∀ {A B C} → A ×ᵗ B →ᵗ C → A →ᵗ B ⇒ᵗ C
  curryᵗ {A} f =
    tset-map
      (λ x → f ∘ᵗ mapˣᵗ (hom-iso-map x) idᵗ)
      (λ p x →
        ≡ᵗ-≡ (eqᵗ (λ { (q , y) →
          cong
            (map-carrier f)
            (cong (_, y) (monotone-trans A p q x)) })))
   
  uncurryᵗ : ∀ {A B C} → A →ᵗ B ⇒ᵗ C → A ×ᵗ B →ᵗ C
  uncurryᵗ {A} {B} {C} f =
    tset-map
      (λ { (x , y) → map-carrier (map-carrier f x) (≤-refl , y) })
      (λ { p (x , y) →
        trans
          (cong
            (λ z → map-carrier z (≤-reflexive refl , monotone B p y))
            (map-nat f p x))
          (trans
            (cong
              (λ q → map-carrier (map-carrier f x) (q , monotone B p y))
              (≤-irrelevant _ _))
            (map-nat (map-carrier f x) p (≤-reflexive refl , y))) })

  map⇒ᵗ-identity : ∀ {A B} → map⇒ᵗ {A} {A} {B} {B} idᵗ idᵗ ≡ᵗ idᵗ
  map⇒ᵗ-identity = eqᵗ (λ f → ≡ᵗ-≡ (eqᵗ (λ x → refl)))

  curryᵗ-mapˣᵗ : ∀ {A B C D E}
               → (f : C ×ᵗ D →ᵗ E) → (g : A →ᵗ C) → (h : B →ᵗ D)
               → curryᵗ (f ∘ᵗ mapˣᵗ g h) ≡ᵗ map⇒ᵗ h idᵗ ∘ᵗ curryᵗ f ∘ᵗ g
  curryᵗ-mapˣᵗ f g h =
    eqᵗ (λ x →
      ≡ᵗ-≡ (eqᵗ (λ y →
        cong (map-carrier f)
          (cong₂ _,_ (map-nat g _ x) refl))))

  uncurryᵗ-mapʳ : ∀ {A B C D}
               → (f : A →ᵗ B)
               → (g : B →ᵗ C ⇒ᵗ D)
               → uncurryᵗ (g ∘ᵗ f)
              ≡ᵗ uncurryᵗ g ∘ᵗ mapˣᵗ f idᵗ
  uncurryᵗ-mapʳ f g =
    eqᵗ (λ xy → refl)

------ packing and unpacking the abstract definitions

abstract
  pack-⇒ᵗ : ∀ {A B t}
          → homᵒ t ×ᵗ A →ᵗ B
          → carrier (A ⇒ᵗ B) t
  pack-⇒ᵗ f = f

  unpack-⇒ᵗ : ∀ {A B t}
            → carrier (A ⇒ᵗ B) t
            → homᵒ t ×ᵗ A →ᵗ B
  unpack-⇒ᵗ f = f

  pack-unpack-⇒ᵗ : ∀ {A B t}
                 → (f : homᵒ t ×ᵗ A →ᵗ B)
                 → unpack-⇒ᵗ {A} {B} {t} (pack-⇒ᵗ f) ≡ f
  pack-unpack-⇒ᵗ xy = refl

  pack-⇒ᵗ-monotone : ∀ {A B t t'}
                   → (p : t ≤ t')
                   → (f : homᵒ t ×ᵗ A →ᵗ B)
                   → monotone (A ⇒ᵗ B) p (pack-⇒ᵗ f)
                   ≡ pack-⇒ᵗ {A} {B} {t'}
                       (tset-map
                         (λ qv →
                           map-carrier f
                             (pack-×ᵗ
                               (pack-homᵒ t (≤-trans p (unpack-homᵒ t' (proj₁ (unpack-×ᵗ qv)))) ,
                                proj₂ (unpack-×ᵗ qv))))
                         (λ q rv →
                           trans
                             (cong (map-carrier f)
                               (trans
                                 (cong pack-×ᵗ
                                   (cong₂ _,_
                                     (trans
                                       (cong (pack-homᵒ t)
                                         (≤-irrelevant _ _))
                                       (sym
                                         (pack-homᵒ-monotone _ _)))
                                     (sym (cong proj₂ (unpack-×ᵗ-monotone q rv)))))
                                 (sym (pack-×ᵗ-monotone _ _))))
                             (map-nat f _ _)))
  pack-⇒ᵗ-monotone p f =
    cong (tset-map _) (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ rv → uip)))))

  unpack-⇒ᵗ-map-carrier : ∀ {A B t t' t''}
                        → (f : carrier (A ⇒ᵗ B) t)
                        → (p : t ≤ t')
                        → (q : t' ≤ t'')
                        → (x : carrier A t'')
                        → map-carrier (unpack-⇒ᵗ (monotone (A ⇒ᵗ B) p f)) (pack-×ᵗ (pack-homᵒ t' q , x))
                        ≡ map-carrier (unpack-⇒ᵗ f) (pack-×ᵗ (pack-homᵒ t (≤-trans p q) , x))
  unpack-⇒ᵗ-map-carrier f p q x = refl

  map⇒ᵗ-reveal : ∀ {A B C D t}
               → (f : A →ᵗ B)
               → (g : C →ᵗ D)
               → (h : carrier (B ⇒ᵗ C) t)
               → map-carrier (map⇒ᵗ f g) h
               ≡ pack-⇒ᵗ
                   (g ∘ᵗ unpack-⇒ᵗ h ∘ᵗ mapˣᵗ idᵗ f)
  map⇒ᵗ-reveal f g h = refl

-}
