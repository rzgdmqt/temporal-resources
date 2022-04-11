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

-- Context split by a variable

var-split : ∀ {Γ A τ}
          → A ∈[ τ ] Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ ∷ᶜ A , Γ₂ split Γ × ctx-delay Γ₂ ≡ τ)

var-split {Γ ∷ᶜ A} Hd = Γ , [] , split-[] , refl
var-split {Γ ∷ᶜ B} (Tl-∷ᶜ x) with var-split x
... | Γ₁ , Γ₂ , p , q = Γ₁ , Γ₂ ∷ᶜ B , split-∷ᶜ p , q
var-split {Γ ⟨ τ ⟩} (Tl-⟨⟩ x) with var-split x
... | Γ₁ , Γ₂ , p , q =
  Γ₁ , Γ₂ ⟨ τ ⟩ , split-⟨⟩ p , trans (cong (_+ τ) q) (+-comm _ τ)

-- Variable in a context is in one of the two contexts splitting it

var-in-split : ∀ {Γ Γ₁ Γ₂ A τ}
             → Γ₁ , Γ₂ split Γ
             → (x : A ∈[ τ ] Γ)
             → (Σ[ Γ' ∈ Ctx ] proj₁ (var-split x) ∷ᶜ A , Γ' split Γ₁)
             ⊎ Σ[ Γ' ∈ Ctx ] Σ[ Γ'' ∈ Ctx ] (Γ' ∷ᶜ A , Γ'' split Γ₂) × Γ₁ ++ᶜ Γ' ≡ proj₁ (var-split x)

var-in-split {Γ₂ = .[]} {A = A} split-[] x with var-split x
... | Γ₁ , Γ₂ , p , q = inj₁ (Γ₂ , p)
var-in-split {Γ₂ = .(_ ∷ᶜ _)} (split-∷ᶜ p) x = {!!}
var-in-split {Γ₂ = .(_ ⟨ _ ⟩)} (split-⟨⟩ p) x = {!!}

-- Substituting a value for a variable

_[_↦_]var : ∀ {Γ A B τ τ'}
          → B ∈[ τ' ] Γ
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          ---------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B
 
Hd [ Hd ↦ W ]var = W
Hd [ Tl-∷ᶜ x ↦ W ]var with var-split x
... | Γ₁ , Γ₂ , p , q = var Hd
Tl-∷ᶜ y [ Hd ↦ W ]var = var y
Tl-∷ᶜ y [ Tl-∷ᶜ x ↦ W ]var with var-split x | inspect var-split x
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
  lam M   [ x ↦ W ]v = lam (M [ Tl-∷ᶜ x ↦ W ]c)
  box V   [ x ↦ W ]v = box (V [ Tl-⟨⟩ x ↦ W ]v)

  _[_↦_]c : ∀ {Γ A C τ}
          → Γ ⊢C⦂ C
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢C⦂ C

  return V       [ x ↦ W ]c = return (V [ x ↦ W ]v)
  (M ; N)        [ x ↦ W ]c = (M [ x ↦ W ]c) ; (N [ Tl-∷ᶜ x ↦ W ]c)
  (V₁ · V₂)      [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  absurd V       [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ᶜ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c {A = A} (unbox p q V M) x W with var-in-split p x
  
  ... | inj₁ (Γ' , r) rewrite sym (split-≡ r) = {!!} --unbox {!!} {!!} {!V [ {!!} ↦ {!!} ]v!} (M [ Tl-∷ᶜ x ↦ W ]c)
  
  ... | inj₂ (Γ' , Γ'' , r , s) = {!!}

--rewrite (sym s) | sym (split-≡ p) | sym (split-≡ r) =

{-

trans
        (cong (_++ᶜ ([] ∷ᶜ A ++ᶜ proj₁ (proj₂ (var-split x)))) s)
        (trans
          (sym (++ᶜ-assoc {proj₁ (var-split x)} {[] ∷ᶜ A} {proj₁ (proj₂ (var-split x))}))
          (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))
          
-}

-- ++ᶜ-injectiveʳ

  {-
    subst (_⊢C⦂ _)
      (sym (++ᶜ-assoc {_} {Γ'} {Γ₂}))
      (unbox {!!} {!!} {!!} (subst (_⊢C⦂ _) {!!} (M [ Tl-∷ᶜ x ↦ {!!} ]c)))
  -}
  
  --  subst (_⊢C⦂ _)
  --    (sym (++ᶜ-assoc {_} {Γ'} {proj₁ (proj₂ (var-split x))}))
  --    (unbox {!!} {!!} V {!M [ Tl-∷ᶜ x ↦ ? ]c!})
  
  --unbox {Γ = {!Γ''' ++ᶜ Γ'!}} {Γ' = {!!}} {!!} {!q!} V (M [ Tl-∷ᶜ x ↦ W ]c)
  --unbox {!!} {!!} {!!} (M [ Tl-∷ᶜ x ↦ W ]c)
  
  coerce p M     [ x ↦ W ]c = coerce p (M [ x ↦ W ]c)
