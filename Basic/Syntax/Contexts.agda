--------------------------------------------
-- Variables and contexts of the language --
--------------------------------------------

open import Data.Product
open import Data.Sum

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Syntax.Types

open import Util.Operations
open import Util.Time

module Syntax.Contexts where

-- Structured contexts

data Ctx : Set where
  []   : Ctx                       -- empty context
  _∷_  : Ctx → VType → Ctx         -- context extension with a variable
  _⟨_⟩ : Ctx → Time → Ctx          -- using context after time-passage

infixl 31 _∷_
infix  32 _⟨_⟩

∷ᶜ-injective : ∀ {Γ Γ' A} → Γ ∷ A ≡ Γ' ∷ A → Γ ≡ Γ'
∷ᶜ-injective refl = refl

⟨⟩-injective : ∀ {Γ Γ' τ} → Γ ⟨ τ ⟩ ≡ Γ' ⟨ τ ⟩ → Γ ≡ Γ'
⟨⟩-injective refl = refl

-- Concatenation of contexts

_++ᶜ_ : Ctx → Ctx → Ctx
Γ ++ᶜ []         = Γ
Γ ++ᶜ (Γ' ∷ X)   = (Γ ++ᶜ Γ') ∷ X
Γ ++ᶜ (Γ' ⟨ τ ⟩) = (Γ ++ᶜ Γ') ⟨ τ ⟩

infixl 30 _++ᶜ_

-- Identity, associativity, and injectivity of ++ᶜ

++ᶜ-identityˡ : ∀ {Γ} → [] ++ᶜ Γ ≡ Γ
++ᶜ-identityˡ {[]}      = refl
++ᶜ-identityˡ {Γ ∷ A}   = cong (_∷ A) ++ᶜ-identityˡ
++ᶜ-identityˡ {Γ ⟨ τ ⟩} = cong (_⟨ τ ⟩) ++ᶜ-identityˡ

++ᶜ-identityʳ : ∀ {Γ} → Γ ++ᶜ [] ≡ Γ
++ᶜ-identityʳ = refl

++ᶜ-assoc : (Γ Γ' Γ'' : Ctx) → (Γ ++ᶜ Γ') ++ᶜ Γ'' ≡ Γ ++ᶜ (Γ' ++ᶜ Γ'')
++ᶜ-assoc Γ Γ' []          = refl
++ᶜ-assoc Γ Γ' (Γ'' ∷ A)   = cong (_∷ A) (++ᶜ-assoc Γ Γ' Γ'')
++ᶜ-assoc Γ Γ' (Γ'' ⟨ τ ⟩) = cong (_⟨ τ ⟩) (++ᶜ-assoc Γ Γ' Γ'')

-- Amount of time-passage modelled by a context 

ctx-time : Ctx → Time
ctx-time []        = 0
ctx-time (Γ ∷ A)   = ctx-time Γ
ctx-time (Γ ⟨ τ ⟩) = ctx-time Γ + τ

-- Interaction of time-passage and ++ᶜ

ctx-time-++ᶜ : (Γ Γ' : Ctx)
              → ctx-time (Γ ++ᶜ Γ') ≡ ctx-time Γ + ctx-time Γ'
ctx-time-++ᶜ Γ []         = sym (+-identityʳ (ctx-time Γ))
ctx-time-++ᶜ Γ (Γ' ∷ A)   = ctx-time-++ᶜ Γ Γ'
ctx-time-++ᶜ Γ (Γ' ⟨ τ ⟩) = trans
                               (cong (_+ τ) (ctx-time-++ᶜ Γ Γ'))
                               (+-assoc (ctx-time Γ) (ctx-time Γ') τ)

-- Proof that sub-contexts split a given context

data _,_split_ : (Γ Γ' Γ'' : Ctx) → Set where
  split-[] : ∀ {Γ} → Γ , [] split Γ
  split-∷  : ∀ {Γ Γ' Γ'' A} → Γ , Γ' split Γ'' → Γ , Γ' ∷ A split Γ'' ∷ A
  split-⟨⟩ : ∀ {Γ Γ' Γ'' τ} → Γ , Γ' split Γ'' → Γ , Γ' ⟨ τ ⟩ split Γ'' ⟨ τ ⟩

-- Interaction between context splitting and ++ᶜ 

split-≡ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → Γ₁ ++ᶜ Γ₂ ≡ Γ
split-≡ split-[]     = refl
split-≡ (split-∷ p)  = cong (_∷ _) (split-≡ p)
split-≡ (split-⟨⟩ p) = cong (_⟨ _ ⟩) (split-≡ p)

≡-split : ∀ {Γ Γ₁ Γ₂} → Γ₁ ++ᶜ Γ₂ ≡ Γ → Γ₁ , Γ₂ split Γ
≡-split {Γ₂ = []}       refl = split-[]
≡-split {Γ₂ = Γ₂ ∷ A}   refl = split-∷ (≡-split refl)
≡-split {Γ₂ = Γ₂ ⟨ τ ⟩} refl = split-⟨⟩ (≡-split refl)

split-≡-++ᶜ : ∀ {Γ₁ Γ₂} → Γ₁ , Γ₂ split (Γ₁ ++ᶜ Γ₂)
split-≡-++ᶜ = ≡-split refl

-- Variable in a context (under τ-amount of time-passage)

data _∈[_]_ (A : VType) : Time → Ctx → Set where
  Hd    : ∀ {Γ}      → A ∈[ 0 ] Γ ∷ A
  Tl-∷  : ∀ {Γ B τ}  → A ∈[ τ ] Γ → A ∈[ τ ] Γ ∷ B
  Tl-⟨⟩ : ∀ {Γ τ τ'} → A ∈[ τ' ] Γ → A ∈[ τ + τ' ] Γ ⟨ τ ⟩

infix 27 _∈[_]_

-- Splitting a context according to a variable in it

var-split : ∀ {Γ A τ}
          → A ∈[ τ ] Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] Γ₁ ∷ A , Γ₂ split Γ × ctx-time Γ₂ ≡ τ

var-split {Γ ∷ A} Hd = Γ , [] , split-[] , refl
var-split {Γ ∷ B} (Tl-∷ x) with var-split x
... | Γ₁ , Γ₂ , p , q = Γ₁ , Γ₂ ∷ B , split-∷ p , q
var-split {Γ ⟨ τ ⟩} (Tl-⟨⟩ x) with var-split x
... | Γ₁ , Γ₂ , p , q =
  Γ₁ , Γ₂ ⟨ τ ⟩ , split-⟨⟩ p , trans (cong (_+ τ) q) (+-comm _ τ)

var-in-split-proj₁-subst : ∀ {Γ A τ τ'}
                         → (x : A ∈[ τ ] Γ)
                         → (p : τ ≡ τ')
                         → proj₁ (var-split x)
                         ≡ proj₁ (var-split (subst (A ∈[_] Γ) p x))

var-in-split-proj₁-subst x refl = refl

var-in-split-proj₂-subst : ∀ {Γ A τ τ'}
                         → (x : A ∈[ τ ] Γ)
                         → (p : τ ≡ τ')
                         → proj₁ (proj₂ (var-split x))
                         ≡ proj₁ (proj₂ (var-split (subst (A ∈[_] Γ) p x)))

var-in-split-proj₂-subst x refl = refl

-- Variable in context is in one of the two contexts splitting it

var-in-split : ∀ {Γ Γ₁ Γ₂ A τ}
             → Γ₁ , Γ₂ split Γ
             → (x : A ∈[ τ ] Γ)
             → (Σ[ y ∈ A ∈[ τ ∸ ctx-time Γ₂ ] Γ₁ ]
                   proj₁ (var-split x) ≡ proj₁ (var-split y)
                 × proj₁ (proj₂ (var-split x)) ≡ proj₁ (proj₂ (var-split y)) ++ᶜ Γ₂)
             ⊎ (Σ[ Γ' ∈ Ctx ] Σ[ Γ'' ∈ Ctx ]
                   (Γ' ∷ A , Γ'' split Γ₂)
                 × Γ₁ ++ᶜ Γ' ≡ proj₁ (var-split x)
                 × Γ'' ≡ proj₁ (proj₂ (var-split x)))

var-in-split split-[] x = inj₁ (x , refl , refl)
var-in-split (split-∷ p) Hd = inj₂ (_ , [] , split-[] , split-≡ p , refl)
var-in-split (split-∷ p) (Tl-∷ {B = B} x) with var-in-split p x
... | inj₁ (y , q , r) = inj₁ (y , q , cong (_∷ B) r)
... | inj₂ (Γ' , Γ'' , q , r , s) =
  inj₂ (Γ' , Γ'' ∷ _ , split-∷ q , r , cong (_∷ B) s)
var-in-split {Γ₁ = Γ₁} {Γ₂ = Γ₂ ⟨ τ ⟩} {A = A}
  (split-⟨⟩ p) (Tl-⟨⟩ {τ' = τ'} x) with var-in-split p x
... | inj₁ (y , q , r) =
  inj₁ (
    subst (A ∈[_] Γ₁)
      (trans
        (trans
          (trans
            (cong (_∸ ctx-time Γ₂)
              (trans
                (trans
                  (sym (+-identityʳ τ'))
                  (cong (τ' +_) (sym (n∸n≡0 τ))))
                (sym (+-∸-assoc τ' (≤-refl {τ})))))
            (∸-+-assoc (τ' + τ) τ (ctx-time Γ₂)))
          (cong (τ' + τ ∸_) (+-comm τ (ctx-time Γ₂))))
        (cong (_∸ (ctx-time Γ₂ + τ)) (+-comm τ' τ))) y ,
    trans q (var-in-split-proj₁-subst y _) ,
    cong (_⟨ τ ⟩) (trans r (cong (_++ᶜ Γ₂) (var-in-split-proj₂-subst y _))))
... | inj₂ (Γ' , Γ'' , q , r , s) =
  inj₂ (Γ' , Γ'' ⟨ τ ⟩ , split-⟨⟩ q , r , cong (_⟨ τ ⟩) s)

-- Temporal contexts (lists of τs, used
-- to type a generalised delay operation)

data TCtx : Set where
  ⦉_⦊  : Time → TCtx
  _⟨_⟩ : TCtx → Time → TCtx

_++ᵗᶜ_ : TCtx → TCtx → TCtx
τs ++ᵗᶜ ⦉ τ ⦊ = τs ⟨ τ ⟩
τs ++ᵗᶜ (τs' ⟨ τ ⟩) = (τs ++ᵗᶜ τs') ⟨ τ ⟩

infixl 30 _++ᵗᶜ_

tctx-time : TCtx → Time
tctx-time ⦉ τ ⦊ = τ
tctx-time (τs ⟨ τ ⟩) = tctx-time τs + τ

++ᵗᶜ-tctx-time : (τs τs' : TCtx)
              → tctx-time (τs ++ᵗᶜ τs') ≡ tctx-time τs + tctx-time τs'
++ᵗᶜ-tctx-time τs ⦉ τ ⦊ = refl
++ᵗᶜ-tctx-time τs (τs' ⟨ τ ⟩) =
  trans
    (cong (_+ τ) (++ᵗᶜ-tctx-time τs τs'))
    (+-assoc (tctx-time τs) (tctx-time τs') τ)

tctx-ctx : TCtx → Ctx
tctx-ctx ⦉ τ ⦊ = [] ⟨ τ ⟩
tctx-ctx (τs ⟨ τ ⟩) = (tctx-ctx τs) ⟨ τ ⟩

++ᵗᶜ-tctx-ctx : (τs τs' : TCtx)
             → tctx-ctx (τs ++ᵗᶜ τs') ≡ tctx-ctx τs ++ᶜ tctx-ctx τs'
++ᵗᶜ-tctx-ctx τs ⦉ τ ⦊ =
  refl
++ᵗᶜ-tctx-ctx τs (τs' ⟨ τ ⟩) =
  cong _⟨ τ ⟩ (++ᵗᶜ-tctx-ctx τs τs')
