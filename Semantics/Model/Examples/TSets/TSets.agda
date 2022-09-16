--------------------------------------------------------
-- Time-varying sets (covariant presheaves on (ℕ,≤)), --
-- their morphisms, and basic categorical structures  --
--------------------------------------------------------

module Semantics.Model.Examples.TSets.TSets where

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

open import Util.Equality hiding (begin_; _≡⟨⟩_; step-≡; _∎)
open import Util.Time

-- Time-varying sets (covariant presheaves on (ℕ,≤))

record TSet : Set₁ where
  constructor
    tset
  field
    -- object map / carrier of the presheaf
    carrier  : Time → Set
    -- functorial action / monotonicity on (ℕ,≤) of the presheaf
    monotone : ∀ {t t'} → t ≤ t' → carrier t → carrier t'
    -- functorial action preserves identities and composition
    monotone-refl  : ∀ {t}
                   → (x : carrier t) → monotone (≤-refl {t}) x ≡ x
    monotone-trans : ∀ {t t' t''} → (p : t ≤ t') → (q : t' ≤ t'')
                   → (x : carrier t) → monotone q (monotone p x) ≡ monotone (≤-trans p q) x

open TSet public

-- Constant time-varying sets

ConstTSet : Set → TSet
ConstTSet A = tset (λ _ → A) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

-- Maps of time-varying sets

record _→ᵗ_ (A B : TSet) : Set where
  constructor
    tset-map
  field
    -- carrier of a map between two presheaves
    map-carrier : ∀ {t} → carrier A t → carrier B t
    -- naturality of the map
    map-nat : ∀ {t t'} → (p : t ≤ t')
            → (x : carrier A t)
            → map-carrier (monotone A p x) ≡ monotone B p (map-carrier x)

infix 20 _→ᵗ_

open _→ᵗ_ public

-- Equality of TSet-morphisms

record _≡ᵗ_ {A B : TSet} (f g : A →ᵗ B) : Set where
  constructor
    eqᵗ
  field
    prf : ∀ {t} → (x : carrier A t) → map-carrier f x ≡ map-carrier g x

open _≡ᵗ_ public

infix 5 _≡ᵗ_

-- ≡ᵗ implies ≡ and vice versa

≡ᵗ-≡ : ∀ {A B} → {f g : A →ᵗ B} → f ≡ᵗ g → f ≡ g
≡ᵗ-≡ p =
  dcong₂
    tset-map
      (ifun-ext (fun-ext (prf p)))
      (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ x → uip)))))
 
≡-≡ᵗ : ∀ {A B} → {f g : A →ᵗ B} → f ≡ g → f ≡ᵗ g
≡-≡ᵗ refl = eqᵗ (λ x → refl)

-- Identity and composition of maps

idᵗ : ∀ {A} → A →ᵗ A
idᵗ = tset-map id (λ p x → refl)
 
_∘ᵗ_ : ∀ {A B C} → B →ᵗ C → A →ᵗ B → A →ᵗ C
g ∘ᵗ f =
  tset-map
    (map-carrier g ∘ map-carrier f)
    (λ p x →
      trans
        (cong (λ y → map-carrier g y) (map-nat f p x))
        (map-nat g p (map-carrier f x)))
 
idᵗ-reveal : ∀ {A}
           → ∀ {t} → (x : carrier A t) → map-carrier (idᵗ {A}) x ≡ x
idᵗ-reveal x = refl
 
∘ᵗ-reveal : ∀ {A B C} → (g : B →ᵗ C) → (f : A →ᵗ B)
          → ∀ {t} → (x : carrier A t) → map-carrier (g ∘ᵗ f) x ≡ map-carrier g (map-carrier f x)
∘ᵗ-reveal g f x = refl

infixr 9 _∘ᵗ_

-- Identity, associativity, and congruence laws

∘ᵗ-identityˡ : ∀ {A B}
             → (f : A →ᵗ B)
             → idᵗ ∘ᵗ f ≡ᵗ f
∘ᵗ-identityˡ f = eqᵗ (λ x → refl)
 
∘ᵗ-identityʳ : ∀ {A B}
             → (f : A →ᵗ B)
             → f ∘ᵗ idᵗ ≡ᵗ f
∘ᵗ-identityʳ f = eqᵗ (λ x → refl)
 
∘ᵗ-assoc : ∀ {A B C D}
         → (h : C →ᵗ D)
         → (g : B →ᵗ C)
         → (f : A →ᵗ B)
         → (h ∘ᵗ g) ∘ᵗ f ≡ᵗ h ∘ᵗ (g ∘ᵗ f)
∘ᵗ-assoc h g f = eqᵗ (λ x → refl)
 
∘ᵗ-congˡ : ∀ {A B C}
         → {f : A →ᵗ B}
         → {g h : B →ᵗ C}
         → g ≡ᵗ h
         → g ∘ᵗ f ≡ᵗ h ∘ᵗ f
∘ᵗ-congˡ {f = f} p =
  eqᵗ (λ x → cong-app (fun-ext (prf p)) (map-carrier f x))
 
∘ᵗ-congʳ : ∀ {A B C}
         → {f g : A →ᵗ B}
         → {h : B →ᵗ C}
         → f ≡ᵗ g
         → h ∘ᵗ f ≡ᵗ h ∘ᵗ g
∘ᵗ-congʳ {h = h} p =
  eqᵗ (λ x → cong (map-carrier h) (prf p x))


-- Product, sum, exponent, etc structures

---- terminal object

𝟙ᵗ : TSet
𝟙ᵗ = tset (λ _ → ⊤) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)
 
terminalᵗ : ∀ {A} → A →ᵗ 𝟙ᵗ
terminalᵗ = tset-map (λ _ → tt) (λ p x → refl)
 
terminalᵗ-unique : ∀ {A} {f : A →ᵗ 𝟙ᵗ}
                 → f ≡ᵗ terminalᵗ
terminalᵗ-unique = eqᵗ (λ x → refl)


---- initial object

𝟘ᵗ : TSet
𝟘ᵗ = tset (λ _ → ⊥) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)
 
initialᵗ : ∀ {A} → 𝟘ᵗ →ᵗ A
initialᵗ = tset-map (λ ()) (λ { p () })
 
initialᵗ-unique : ∀ {A} {f : 𝟘ᵗ →ᵗ A}
                → f ≡ᵗ initialᵗ
initialᵗ-unique = eqᵗ (λ ())


---- binary products

_×ᵗ_ : TSet → TSet → TSet
A ×ᵗ B =
  tset
    (λ t → carrier A t × carrier B t)
    (λ p → mapˣ (monotone A p) (monotone B p))
    (λ x → cong₂ _,_ (monotone-refl A (proj₁ x)) (monotone-refl B (proj₂ x)))
    (λ p q x → cong₂ _,_ (monotone-trans A p q (proj₁ x)) (monotone-trans B p q (proj₂ x)))

infixr 23 _×ᵗ_

fstᵗ : ∀ {A B} → A ×ᵗ B →ᵗ A
fstᵗ = tset-map proj₁ (λ { p (x , y) → refl })
 
sndᵗ : ∀ {A B} → A ×ᵗ B →ᵗ B
sndᵗ = tset-map proj₂ (λ { p (x , y) → refl })
 
⟨_,_⟩ᵗ : ∀ {A B C} → A →ᵗ B → A →ᵗ C → A →ᵗ B ×ᵗ C
⟨ f , g ⟩ᵗ =
  tset-map
    < map-carrier f , map-carrier g >
    (λ p x → cong₂ _,_ (map-nat f p x) (map-nat g p x))

mapˣᵗ : ∀ {A B C D} → A →ᵗ C → B →ᵗ D → A ×ᵗ B →ᵗ C ×ᵗ D
mapˣᵗ f g = ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ
 
×ᵗ-assoc : ∀ {A B C} → A ×ᵗ (B ×ᵗ C) →ᵗ (A ×ᵗ B) ×ᵗ C
×ᵗ-assoc = ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ
 
×ᵗ-assoc⁻¹ : ∀ {A B C} → (A ×ᵗ B) ×ᵗ C →ᵗ A ×ᵗ (B ×ᵗ C)
×ᵗ-assoc⁻¹ = ⟨ fstᵗ ∘ᵗ fstᵗ , ⟨ sndᵗ ∘ᵗ fstᵗ , sndᵗ ⟩ᵗ ⟩ᵗ

×ᵗ-swap : ∀ {A B} → A ×ᵗ B →ᵗ B ×ᵗ A
×ᵗ-swap = ⟨ sndᵗ , fstᵗ ⟩ᵗ

⟨⟩ᵗ-fstᵗ : ∀ {A B C}
         → (f : A →ᵗ B)
         → (g : A →ᵗ C)
         → fstᵗ ∘ᵗ ⟨ f , g ⟩ᵗ ≡ᵗ f
⟨⟩ᵗ-fstᵗ f g = eqᵗ (λ x → refl)
 
⟨⟩ᵗ-sndᵗ : ∀ {A B C}
         → (f : A →ᵗ B)
         → (g : A →ᵗ C)
         → sndᵗ ∘ᵗ ⟨ f , g ⟩ᵗ ≡ᵗ g
⟨⟩ᵗ-sndᵗ f g = eqᵗ (λ x → refl)
 
⟨⟩ᵗ-unique : ∀ {A B C} → (f : A →ᵗ B) → (g : A →ᵗ C) → (h : A →ᵗ B ×ᵗ C)
           → fstᵗ ∘ᵗ h ≡ᵗ f → sndᵗ ∘ᵗ h ≡ᵗ g
           → h ≡ᵗ ⟨ f , g ⟩ᵗ
⟨⟩ᵗ-unique f g h (eqᵗ p) (eqᵗ q) =
  eqᵗ (λ x → cong₂ _,_ (p x) (q x))
 
mapˣᵗ-×ᵗ-assoc : ∀ {A B C A' B' C'}
               → (f : A →ᵗ A') (g : B →ᵗ B') (h : C →ᵗ C')
               → mapˣᵗ (mapˣᵗ f g) h ∘ᵗ ×ᵗ-assoc
              ≡ᵗ ×ᵗ-assoc ∘ᵗ mapˣᵗ f (mapˣᵗ g h)
mapˣᵗ-×ᵗ-assoc f g h =
  eqᵗ (λ xyz → refl)

mapˣᵗ-∘ᵗ : ∀ {A A' A'' B B' B''}
         → (f : A →ᵗ A') (g : B →ᵗ B') (h : A' →ᵗ A'') (i : B' →ᵗ B'')
         → mapˣᵗ (h ∘ᵗ f) (i ∘ᵗ g)
        ≡ᵗ mapˣᵗ h i ∘ᵗ mapˣᵗ f g
mapˣᵗ-∘ᵗ f g h i =
  eqᵗ (λ xy → refl)


---- Set-indexed products

Π : (I : Set) → (I → TSet) → TSet
Π I A =
  tset
    (λ τ → (i : I) → carrier (A i) τ)
    (λ p f i → monotone (A i) p (f i))
    (λ f → fun-ext (λ i → monotone-refl (A i) (f i)))
    (λ p q f → fun-ext (λ i → monotone-trans (A i) p q (f i)))
 
projᵗ : ∀ {I A} → (i : I) → Π I A →ᵗ A i
projᵗ i =
  tset-map
    (λ f → f i)
    (λ p f → refl)
    
⟨_⟩ᵢᵗ : ∀ {I A B} → ((i : I) → A →ᵗ B i) → A →ᵗ Π I B
⟨ fs ⟩ᵢᵗ =
  tset-map
    (λ x i → map-carrier (fs i) x)
    (λ p x → fun-ext (λ i → map-nat (fs i) p x))
   
mapⁱˣᵗ : ∀ {I A B} → ((i : I) → A i →ᵗ B i) → Π I A →ᵗ Π I B
mapⁱˣᵗ fs = ⟨ (λ i → fs i ∘ᵗ projᵗ i) ⟩ᵢᵗ

mapⁱˣᵗ-identity : ∀ {I A}
                → mapⁱˣᵗ {I} {A} {A} (λ i → idᵗ) ≡ᵗ idᵗ
mapⁱˣᵗ-identity =
  eqᵗ (λ f → refl)
 
mapⁱˣᵗ-∘ᵗ : ∀ {I} {A B C : I → TSet}
          → (f : ((i : I) → A i →ᵗ B i))
          → (g : ((i : I) → B i →ᵗ C i))
          → mapⁱˣᵗ (λ i → g i ∘ᵗ f i)
         ≡ᵗ mapⁱˣᵗ g ∘ᵗ mapⁱˣᵗ f
mapⁱˣᵗ-∘ᵗ f g =
  eqᵗ (λ h → refl)
 
⟨⟩ᵢᵗ-projᵗ : ∀ {I} {A} {B : I → TSet}
           → (f : ((i : I) → A →ᵗ B i))
           → (i : I)
           → projᵗ i ∘ᵗ ⟨ f ⟩ᵢᵗ ≡ᵗ f i
⟨⟩ᵢᵗ-projᵗ f i = eqᵗ (λ x → refl)
 
⟨⟩ᵢᵗ-∘ᵗ : ∀ {I} {A B} {C : I → TSet}
        → (f : A →ᵗ B)
        → (g : ((i : I) → B →ᵗ C i))
        → ⟨ (λ i → g i ∘ᵗ f) ⟩ᵢᵗ
       ≡ᵗ ⟨ g ⟩ᵢᵗ ∘ᵗ f
⟨⟩ᵢᵗ-∘ᵗ f g =
  eqᵗ (λ x → refl)


---- covariant hom-functor

homᵒ : Time → TSet
homᵒ t =
  tset
    (λ t' → t ≤ t')
    (λ p q → ≤-trans q p)
    (λ p → ≤-irrelevant _ _)
    (λ p q r → ≤-irrelevant _ _)
 
homᶠ : ∀ {t t'} → t ≤ t' → homᵒ t' →ᵗ homᵒ t
homᶠ p =
  tset-map
    (λ q → ≤-trans p q)
    (λ p q → ≤-irrelevant _ _)
 
homᶠ-refl : ∀ {t} → homᶠ (≤-refl {t}) ≡ᵗ idᵗ
homᶠ-refl = eqᵗ λ p → ≤-irrelevant _ _
 
homᶠ-trans : ∀ {t t' t''}
           → (p : t ≤ t') → (q : t' ≤ t'')
           → homᶠ p ∘ᵗ homᶠ q ≡ᵗ homᶠ (≤-trans p q)
homᶠ-trans p q = eqᵗ (λ r → ≤-irrelevant _ _)
 
hom-iso-map : ∀ {A t} → carrier A t → homᵒ t →ᵗ A
hom-iso-map {A} x =
  tset-map
    (λ p → monotone A p x)
    (λ p q → sym (monotone-trans A q p x))
 
hom-iso-map⁻¹ : ∀ {A t} → homᵒ t →ᵗ A → carrier A t
hom-iso-map⁻¹ {A} f = map-carrier f ≤-refl


---- exponentials

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
