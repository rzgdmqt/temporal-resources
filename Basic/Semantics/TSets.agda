--------------------------------------------------------
-- Time-varying sets (covariant presheaves on (ℕ,≤)), --
-- their morphisms, and basic categorical structures  --
--------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

open import Util.Equality
open import Util.Time

module Semantics.TSets where

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

    -- TODO: also include naturality law

infix 20 _→ᵗ_

open _→ᵗ_ public

-- Equality of TSet-morphisms

_≡ᵗ_ : ∀ {A B} → A →ᵗ B → A →ᵗ B → Set
_≡ᵗ_ {A} f g = ∀ {t} → (x : carrier A t) → map-carrier f x ≡ map-carrier g x

infix 5 _≡ᵗ_

-- ≡ᵗ implies ≡

≡ᵗ-≡ : ∀ {A B} → {f : A →ᵗ B} {g : A →ᵗ B} → f ≡ᵗ g → f ≡ g
≡ᵗ-≡ p =
  dcong₂
    tset-map
      (ifun-ext (fun-ext p))
      (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ x → uip)))))

-- Begin-qed style reasoning for ≡ᵗ

infix  3 _∎
infixr 2 _≡⟨⟩_ step-≡
infix  1 begin_

begin_ : ∀ {A B} {f g : A →ᵗ B} → f ≡ᵗ g → f ≡ᵗ g
begin_ f≡g = f≡g

_≡⟨⟩_ : ∀ {A B} (f {g} : A →ᵗ B) → f ≡ᵗ g → f ≡ᵗ g
_ ≡⟨⟩ f≡g = f≡g

step-≡ : ∀ {A B} (f {g h} : A →ᵗ B) → g ≡ᵗ h → f ≡ᵗ g → f ≡ᵗ h
step-≡ _ g≡h f≡g = λ x → trans (f≡g x) (g≡h x)

_∎ : ∀ {A B} (f : A →ᵗ B) → f ≡ᵗ f
_∎ _ = λ x → refl

syntax step-≡ f g≡h f≡g = f ≡⟨ f≡g ⟩ g≡h

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

infixr 9 _∘ᵗ_

-- Product, sum, exponent, etc structures

---- terminal object

𝟙ᵗ : TSet
𝟙ᵗ = tset (λ _ → ⊤) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

terminalᵗ : ∀ {A} → A →ᵗ 𝟙ᵗ
terminalᵗ = tset-map (λ _ → tt) (λ p x → refl)

---- initial object

𝟘ᵗ : TSet
𝟘ᵗ = tset (λ _ → ⊥) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

initialᵗ : ∀ {A} → 𝟘ᵗ →ᵗ A
initialᵗ = tset-map (λ ()) (λ { p () })

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

×-assocᵗ : ∀ {A B C} → A ×ᵗ (B ×ᵗ C) →ᵗ (A ×ᵗ B) ×ᵗ C
×-assocᵗ = ⟨ ⟨ fstᵗ , fstᵗ ∘ᵗ sndᵗ ⟩ᵗ , sndᵗ ∘ᵗ sndᵗ ⟩ᵗ

×-assocᵗ⁻¹ : ∀ {A B C} → (A ×ᵗ B) ×ᵗ C →ᵗ A ×ᵗ (B ×ᵗ C)
×-assocᵗ⁻¹ = ⟨ fstᵗ ∘ᵗ fstᵗ , ⟨ sndᵗ ∘ᵗ fstᵗ , sndᵗ ⟩ᵗ ⟩ᵗ

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
    
⟨_⟩ᵢᵗ : ∀ {A I B} → ((i : I) → A →ᵗ B i) → A →ᵗ Π I B
⟨ fs ⟩ᵢᵗ =
  tset-map
    (λ x i → map-carrier (fs i) x)
    (λ p x → fun-ext (λ i → map-nat (fs i) p x))

mapⁱˣᵗ : ∀ {I A B} → ((i : I) → A i →ᵗ B i) → Π I A →ᵗ Π I B
mapⁱˣᵗ fs = ⟨ (λ i → fs i ∘ᵗ projᵗ i) ⟩ᵢᵗ

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
homᶠ-refl p = ≤-irrelevant _ _

homᶠ-trans : ∀ {t t' t''}
           → (p : t ≤ t') → (q : t' ≤ t'')
           → homᶠ p ∘ᵗ homᶠ q ≡ᵗ homᶠ (≤-trans p q)
homᶠ-trans p q r = ≤-irrelevant _ _

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
      ≡ᵗ-≡ (λ { (p , x) →
        cong (λ q → map-carrier f (q , x)) (≤-irrelevant _ _) }))
    (λ p q f →
      ≡ᵗ-≡ (λ { (r , x) →
        cong (λ s → map-carrier f (s , x)) (≤-irrelevant _ _) }))

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
    (λ p h → ≡ᵗ-≡ (λ { (q , x) → refl }))

curryᵗ : ∀ {A B C} → A ×ᵗ B →ᵗ C → A →ᵗ B ⇒ᵗ C
curryᵗ {A} f =
  tset-map
    (λ x → f ∘ᵗ mapˣᵗ (hom-iso-map x) idᵗ)
    (λ p x →
      ≡ᵗ-≡ (λ { (q , y) →
        cong
          (map-carrier f)
          (cong (_, y) (monotone-trans A p q x)) }))

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
