-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Function hiding (const)

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Util.Equality
open import Util.Time

module Syntax.Substitutions where

-- Deciding whether a variable is in the context after time travelling

---- When the variable is in the resulting context

var-in-ctx-after-ᶜ : ∀ {Γ A τ τ'}
                   → (x : A ∈[ τ ] Γ)
                   → τ' ≤ τ
                   → Σ[ y ∈ A ∈[ τ ∸ τ' ] Γ -ᶜ τ' ]
                       (  proj₁ (var-split x) ≡ proj₁ (var-split y)
                        × proj₁ (var-split y) ++ᶜ proj₁ (proj₂ (var-split y))
                          ≡ (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) -ᶜ τ'))
                          
var-in-ctx-after-ᶜ {Γ} {A} {τ} {zero} x p = x , refl , refl
var-in-ctx-after-ᶜ {Γ ∷ B} {A} {τ} {suc τ'} (Tl-∷ x) p with var-in-ctx-after-ᶜ x p
... | y , q , r = y , q , r
var-in-ctx-after-ᶜ {Γ ⟨ τ'' ⟩} {A} {.(τ'' + _)} {suc τ'} (Tl-⟨⟩ x) p with suc τ' ≤? τ''
var-in-ctx-after-ᶜ {Γ ⟨ τ'' ⟩} {A} {.(τ'' + _)} {suc τ'} (Tl-⟨⟩ {τ' = τ'''} x) p | yes q
  rewrite trans                                              -- : τ'' + τ''' ∸ suc τ' ≡ (τ'' ∸ suc τ') + τ'''
            (cong (_∸ suc τ') (+-comm τ'' τ'''))
            (trans
              (+-∸-assoc τ''' q)
              (+-comm τ''' (τ'' ∸ suc τ'))) =
  Tl-⟨⟩ x , refl , refl
var-in-ctx-after-ᶜ {Γ ⟨ τ'' ⟩} {A} {.(τ'' + _)} {suc τ'} (Tl-⟨⟩ {τ' = τ'''} x) p | no ¬q
  rewrite trans                                              -- : τ'' + τ''' ∸ suc τ' ≡ τ''' ∸ (suc τ' ∸ τ'')
            (cong (_∸ suc τ') (+-comm τ'' τ'''))
            (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {τ'''} {τ''} {suc τ'} ¬q
              (≤-trans (∸-monoˡ-≤ τ'' p) (≤-reflexive (m+n∸m≡n τ'' τ''')))) =
  var-in-ctx-after-ᶜ {Γ} {τ' = suc τ' ∸ τ''} x
    (≤-trans
      (∸-monoˡ-≤ τ'' p)
      (≤-reflexive (m+n∸m≡n τ'' τ''')))

---- When the variable is not in the resulting context

var-not-in-ctx-after-ᶜ : ∀ {Γ A τ τ'}
                       → (x : A ∈[ τ ] Γ)
                       → τ' > τ
                       → Ren (Γ -ᶜ τ') (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) -ᶜ τ')

var-not-in-ctx-after-ᶜ {Γ ∷ B} {.B} {.0} {suc τ'} Hd p =
  id-ren
var-not-in-ctx-after-ᶜ {Γ ∷ B} {A} {τ} {suc τ'} (Tl-∷ x) p =
  var-not-in-ctx-after-ᶜ {Γ} {τ' = suc τ'} x p
var-not-in-ctx-after-ᶜ {Γ ⟨ τ'' ⟩} {A} {.(τ'' + _)} {suc τ'} (Tl-⟨⟩ {τ' = τ'''} x) (s≤s p) with suc τ' ≤? τ''
... | yes q =
  ⊥-elim (sucn≤m⇒m+k≤n-contradiction q p)
... | no ¬q =
  var-not-in-ctx-after-ᶜ {Γ} {τ' = suc τ' ∸ τ''} x
    (≤-trans
      (≤-trans
        (+-monoʳ-≤ 1 (≤-reflexive (sym (m+n∸m≡n τ'' τ'''))))
        (≤-reflexive (sym (+-∸-assoc 1 {τ'' + τ'''} {τ''} (≤-stepsʳ τ''' ≤-refl)))))
      (∸-monoˡ-≤ τ'' (+-monoʳ-≤ 1 p)))

-- Substituting a value for a variable in context

_[_↦_]var : ∀ {Γ A B τ τ'}
          → B ∈[ τ' ] Γ
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
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
  handle M `with H `in N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with (λ op τ'' → (H op τ'') [ Tl-∷ (Tl-∷ x) ↦ W ]c)
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c {τ = τ} (unbox {τ = τ'} V M) x W with τ' ≤? τ
  _[_↦_]c {τ = τ} (unbox {τ = τ'} V M) x W | yes p with var-in-ctx-after-ᶜ x p
  ... | y , q , r =
    unbox
      (V-rename (eq-ren r) (V [ y ↦ V-rename (eq-ren q) W ]v))
      (M [ Tl-∷ x ↦ W ]c)
  _[_↦_]c {τ = τ} (unbox {τ = τ'} V M) x W | no ¬p =
    unbox (V-rename (var-not-in-ctx-after-ᶜ x (≰⇒> ¬p)) V) (M [ Tl-∷ x ↦ W ]c)
  delay τ p M [ x ↦ W ]c =
    delay τ p (M [ Tl-⟨⟩ x ↦ W ]c)













{-
-- TODO: old stuff, delete at some point

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
  handle M `with H `in N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with (λ op τ'' → (H op τ'') [ Tl-∷ (Tl-∷ x) ↦ W ]c)
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
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
  delay τs p M [ x ↦ W ]c =
    delay τs p
      (C-rename
        (eq-ren
          (trans
            (trans
              (cong
                (proj₁ (var-split
                  (proj₂ (proj₂ (var-rename (wk-ctx-ren {Γ' = tctx-ctx τs}) x)))) ++ᶜ_)
                (sym (var-split₂-wk-ctx-ren {Γ' = tctx-ctx τs} x)))
              (sym
                (++ᶜ-assoc
                   (proj₁ (var-split
                     (proj₂ (proj₂ (var-rename (wk-ctx-ren {Γ' = tctx-ctx τs}) x)))))
                   (proj₁ (proj₂ (var-split x)))
                   (tctx-ctx τs))))
            (cong
              (λ Γ → Γ ++ᶜ proj₁ (proj₂ (var-split x)) ++ᶜ tctx-ctx τs)
              (sym (var-split₁-wk-ctx-ren {Γ' = tctx-ctx τs} x)) )))
        (M [ proj₂ (proj₂ (var-rename (wk-ctx-ren) x))
             ↦
             V-rename (eq-ren (var-split₁-wk-ctx-ren {Γ' = tctx-ctx τs} x)) W ]c))
-}
