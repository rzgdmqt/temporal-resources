-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Data.Product
open import Data.Sum

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Util.Time

module Syntax.Substitutions where

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
  V-rename wk-⟨⟩-ren (y [ x ↦ W ]var)

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

  return V [ x ↦ W ]c =
    return (V [ x ↦ W ]v)
  (M ; N) [ x ↦ W ]c =
    (M [ x ↦ W ]c) ; (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂) [ x ↦ W ]c =
    (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  absurd V [ x ↦ W ]c =
    absurd (V [ x ↦ W ]v)
  perform op V M [ x ↦ W ]c =
    perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  {-handle M `with H `in N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with (λ op τ'' → (H op τ'') [ Tl-∷ (Tl-∷ x) ↦ W ]c)
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)-}
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
            (≤-reflexive (cong ctx-time (sym (split-≡ r))))
            (≤-reflexive (ctx-time-++ᶜ (Γ''' ∷ A) Γ'')))
          (≤-reflexive (sym (ctx-time-++ᶜ Γ''' Γ'' )))))
      V
      (M [ Tl-∷ x ↦ W ]c)
  delay τ p M [ x ↦ W ]c =
    delay τ p (M [ Tl-⟨⟩ x ↦ W ]c)
