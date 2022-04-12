-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

open import Language
open import Renamings

module Substitutions where

-- Splitting a context according to a variable in it

var-split : ∀ {Γ A τ}
          → A ∈[ τ ] Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] Γ₁ ∷ A , Γ₂ split Γ × ctx-delay Γ₂ ≡ τ

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
             → (Σ[ y ∈ A ∈[ τ ∸ ctx-delay Γ₂ ] Γ₁ ]
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
            (cong (_∸ ctx-delay Γ₂)
              (trans
                (trans
                  (sym (+-identityʳ τ'))
                  (cong (τ' +_) (sym (n∸n≡0 τ))))
                (sym (+-∸-assoc τ' (≤-refl {τ})))))
            (∸-+-assoc (τ' + τ) τ (ctx-delay Γ₂)))
          (cong (τ' + τ ∸_) (+-comm τ (ctx-delay Γ₂))))
        (cong (_∸ (ctx-delay Γ₂ + τ)) (+-comm τ' τ))) y ,
    trans q (var-in-split-proj₁-subst y _) ,
    cong (_⟨ τ ⟩) (trans r (cong (_++ᶜ Γ₂) (var-in-split-proj₂-subst y _))))
... | inj₂ (Γ' , Γ'' , q , r , s) =
  inj₂ (Γ' , Γ'' ⟨ τ ⟩ , split-⟨⟩ q , r , cong (_⟨ τ ⟩) s)

-- Substituting a value for a variable in context

_[_↦_]var : ∀ {Γ A B τ τ'}
          → B ∈[ τ' ] Γ
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          ---------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B
 
Hd [ Hd ↦ W ]var = W
Hd [ Tl-∷ x ↦ W ]var with var-split x
... | Γ₁ , Γ₂ , p , q = var Hd
Tl-∷ y [ Hd ↦ W ]var = var y
Tl-∷ y [ Tl-∷ x ↦ W ]var with var-split x | inspect var-split x
... | ._ , ._ , ._ , ._ | [| refl |] =
  V-rename wk-ren (y [ x ↦ W ]var)
Tl-⟨⟩ y [ Tl-⟨⟩ x ↦ W ]var with var-split x | inspect var-split x
... | ._ , ._ , ._ , ._ | [| refl |] =
  V-rename (⟨⟩-mon-ren z≤n ∘ʳ ⟨⟩-eta⁻¹-ren) (y [ x ↦ W ]var)

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B τ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  var y   [ x ↦ W ]v = y [ x ↦ W ]var
  const c [ x ↦ W ]v = const c
  ⋆       [ x ↦ W ]v = ⋆
  lam M   [ x ↦ W ]v = lam (M [ Tl-∷ x ↦ W ]c)
  box V   [ x ↦ W ]v = box (V [ Tl-⟨⟩ x ↦ W ]v)

  _[_↦_]c : ∀ {Γ A C τ}
          → Γ ⊢C⦂ C
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢C⦂ C

  return V       [ x ↦ W ]c = return (V [ x ↦ W ]v)
  (M ; N)        [ x ↦ W ]c = (M [ x ↦ W ]c) ; (N [ Tl-∷ x ↦ W ]c)
  (V₁ · V₂)      [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  absurd V       [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c {A = A} (unbox {Γ' = Γ'} {Γ'' = Γ''} p q V M) x W with var-in-split p x
  ... | inj₁ (y , r , s) =
    unbox
      {Γ'' = Γ'' }
      (≡-split (trans
                 (++ᶜ-assoc (proj₁ (var-split y)) (proj₁ (proj₂ (var-split y))) Γ'')
                 (cong₂ _++ᶜ_ (sym r) (sym s))))
      q
      (V [ y ↦ V-rename (eq-ren r) W ]v)
      (M [ Tl-∷ x ↦ W ]c)
  ... | inj₂ (Γ''' , Γ'' , r , s , u) =
    unbox
      {Γ'' = Γ''' ++ᶜ Γ''}
      (≡-split (trans
                 (sym (++ᶜ-assoc Γ' Γ''' Γ''))
                 (cong₂ _++ᶜ_ s u)))
      (≤-trans
        q
        (≤-trans
          (≤-trans
            (≤-reflexive (cong ctx-delay (sym (split-≡ r))))
            (≤-reflexive (ctx-delay-++ᶜ (Γ''' ∷ A) Γ'')))
          (≤-reflexive (sym (ctx-delay-++ᶜ Γ''' Γ'' )))))
      V
      (M [ Tl-∷ x ↦ W ]c)
  coerce p M     [ x ↦ W ]c = coerce p (M [ x ↦ W ]c)  
