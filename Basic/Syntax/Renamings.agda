------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

open import Function hiding (const)

open import Data.Bool hiding (_≤_)
open import Data.Product
open import Data.Sum

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Util.Time

module Syntax.Renamings where

-- Variable renamings

-- Note 1: This allows one to move a variable under more ⟨_⟩s but not vice versa.
-- Note 2: This disallows the time-passage modelled by the context to decrease.

RenMap : Ctx → Ctx → Set
RenMap Γ Γ' = ∀ {A τ} → A ∈[ τ ] Γ → Σ[ τ' ∈ Time ] (τ ≤ τ' × A ∈[ τ' ] Γ')

record Ren (Γ Γ' : Ctx) : Set where
  constructor
    ren
  field
    ren-map : RenMap Γ Γ'
    ren-≤   : ctx-time Γ ≤ ctx-time Γ'

open Ren public

-- Identity renaming

id-ren-map : ∀ {Γ} → RenMap Γ Γ
id-ren-map {.(_ ∷ _)}   Hd        = _ , ≤-refl , Hd
id-ren-map {.(_ ∷ _)}   (Tl-∷ x)  = _ , ≤-refl , Tl-∷ x
id-ren-map {.(_ ⟨ _ ⟩)} (Tl-⟨⟩ x) = _ , ≤-refl , Tl-⟨⟩ x

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren = ren id-ren-map ≤-refl

-- Composition of renamings

_∘ʳᵐ_ : ∀ {Γ Γ' Γ''} → RenMap Γ' Γ'' → RenMap Γ Γ' → RenMap Γ Γ''
(ρ' ∘ʳᵐ ρ) {A} {τ} Hd with ρ {A} {τ} Hd
... | τ , p , x with ρ' x
... | τ' , p' , y = τ' , ≤-trans p p' , y
(ρ' ∘ʳᵐ ρ) (Tl-∷ x) = (ρ' ∘ʳᵐ (ρ ∘ Tl-∷)) x
(ρ' ∘ʳᵐ ρ) (Tl-⟨⟩ x) with ρ (Tl-⟨⟩ x)
... | τ , p , y with ρ' y
... | τ' , p' , z = τ' , ≤-trans p p' , z

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
ρ' ∘ʳ ρ =
  ren
    (ren-map ρ' ∘ʳᵐ ren-map ρ)
    (≤-trans (ren-≤ ρ) (ren-≤ ρ'))

infixr 20 _∘ʳ_
infixr 20 _∘ʳᵐ_

-- Variable weakening renaming

wk-ren-map : ∀ {Γ A} → RenMap Γ (Γ ∷ A)
wk-ren-map x = _ , ≤-refl , Tl-∷ x

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ A)
wk-ren = ren wk-ren-map ≤-refl

wk-ctx-ren-map : ∀ {Γ Γ'} → RenMap Γ (Γ ++ᶜ Γ')
wk-ctx-ren-map {Γ' = []}       x = _ , ≤-refl , x
wk-ctx-ren-map {Γ' = Γ' ∷ A}   x with wk-ctx-ren-map {Γ' = Γ'} x
... | τ' , p , y = τ' , p , Tl-∷ y
wk-ctx-ren-map {Γ' = Γ' ⟨ τ ⟩} x with wk-ctx-ren-map {Γ' = Γ'} x
... | τ' , p , y = τ + τ' , ≤-stepsˡ τ p , Tl-⟨⟩ y

wk-ctx-ren : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-ren {Γ} {Γ'} =
  ren
    wk-ctx-ren-map
    (≤-trans
      (≤-stepsʳ (ctx-time Γ') ≤-refl)
      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))

-- Exchange renamings

exch-ren-map : ∀ {Γ A B} → RenMap (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren-map Hd              = _ , ≤-refl , Tl-∷ Hd
exch-ren-map (Tl-∷ Hd)       = _ , ≤-refl , Hd
exch-ren-map (Tl-∷ (Tl-∷ x)) = _ , ≤-refl , Tl-∷ (Tl-∷ x)

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = ren exch-ren-map ≤-refl

exch-⟨⟩-var-ren-map : ∀ {Γ A τ} → RenMap (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren-map Hd               = _ , z≤n , Tl-⟨⟩ Hd
exch-⟨⟩-var-ren-map (Tl-∷ (Tl-⟨⟩ x)) = _ , ≤-refl , Tl-⟨⟩ (Tl-∷ x)

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren = ren exch-⟨⟩-var-ren-map ≤-refl

exch-⟨⟩-⟨⟩-ren-map : ∀ {Γ τ τ'} → RenMap (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ' ⟩ ⟨ τ ⟩)
exch-⟨⟩-⟨⟩-ren-map {τ = τ} {τ' = τ'} (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  τ + (τ' + τ'') ,
  ≤-reflexive
    (trans
      (sym (+-assoc τ' τ τ''))
      (trans
        (cong (_+ τ'') (+-comm τ' τ))
        (+-assoc τ τ' τ''))) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

exch-⟨⟩-⟨⟩-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ' ⟩ ⟨ τ ⟩)
exch-⟨⟩-⟨⟩-ren {Γ} {τ} {τ'} =
  ren
    exch-⟨⟩-⟨⟩-ren-map
    (≤-reflexive
      (trans
        (+-assoc (ctx-time Γ) τ τ')
        (trans
          (cong (ctx-time Γ +_) (+-comm τ τ'))
          (sym (+-assoc (ctx-time Γ) τ' τ)))))

-- Contraction renaming

contract-ren-map : ∀ {Γ A} → RenMap (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren-map Hd       = _ , ≤-refl , Hd
contract-ren-map (Tl-∷ x) = _ , ≤-refl , x

contract-ren : ∀ {Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren = ren contract-ren-map ≤-refl

-- Extending a renaming

extend-ren-map : ∀ {Γ Γ' A τ} → RenMap Γ Γ' → A ∈[ τ ] Γ' → RenMap (Γ ∷ A) Γ'
extend-ren-map ρ x Hd       = _ , z≤n , x
extend-ren-map ρ x (Tl-∷ y) = ρ y

extend-ren : ∀ {Γ Γ' A τ} → Ren Γ Γ' → A ∈[ τ ] Γ' → Ren (Γ ∷ A) Γ'
extend-ren ρ x = ren (extend-ren-map (ren-map ρ) x) (ren-≤ ρ)

-- Congruence of context renamings

cong-ren-map : ∀ {Γ Γ' Γ''} → RenMap Γ Γ' → RenMap (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren-map {Γ'' = []} ρ x = ρ x
cong-ren-map {Γ'' = Γ'' ∷ A} ρ Hd = _ , ≤-refl , Hd
cong-ren-map {Γ'' = Γ'' ∷ A} ρ (Tl-∷ x) with cong-ren-map ρ x
... | τ' , p , y = τ' , p , Tl-∷ y
cong-ren-map {Γ'' = Γ'' ⟨ τ ⟩} ρ (Tl-⟨⟩ x) with cong-ren-map ρ x
... | τ' , p , y = τ + τ' , +-monoʳ-≤ τ p , Tl-⟨⟩ y

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ} {Γ'} {Γ''} ρ =
  ren
    (cong-ren-map (ren-map ρ))
    (≤-trans
      (≤-reflexive (ctx-time-++ᶜ Γ Γ''))
      (≤-trans
        (+-monoˡ-≤ (ctx-time Γ'') (ren-≤ ρ))
        (≤-reflexive (sym (ctx-time-++ᶜ Γ' Γ'')))))

-- Unit of ⟨_⟩ (and its inverse)

⟨⟩-η-ren-map : ∀ {Γ} → RenMap (Γ ⟨ 0 ⟩) Γ
⟨⟩-η-ren-map (Tl-⟨⟩ x) = _ , ≤-refl , x

⟨⟩-η-ren : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
⟨⟩-η-ren {Γ} =
  ren
    ⟨⟩-η-ren-map
    (≤-reflexive (+-identityʳ (ctx-time Γ)))

⟨⟩-η⁻¹-ren-map : ∀ {Γ} → RenMap Γ (Γ ⟨ 0 ⟩)
⟨⟩-η⁻¹-ren-map x = _ , ≤-refl , Tl-⟨⟩ x

⟨⟩-η⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
⟨⟩-η⁻¹-ren {Γ} =
  ren
    ⟨⟩-η⁻¹-ren-map
    (≤-reflexive (sym (+-identityʳ (ctx-time Γ))))

-- Multiplication of ⟨_⟩ (and its inverse)

⟨⟩-μ-ren-map : ∀ {Γ τ τ'} → RenMap (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-μ-ren-map {τ = τ} {τ' = τ'} (Tl-⟨⟩ {τ' = τ''} x) =
  _ ,
  ≤-reflexive (trans
                (cong (_+ τ'') (+-comm τ τ'))
                (+-assoc τ' τ τ'')) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-μ-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-μ-ren {Γ} {τ} {τ'} =
  ren
    ⟨⟩-μ-ren-map
    (≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ')))

⟨⟩-μ⁻¹-ren-map : ∀ {Γ τ τ'} → RenMap (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-μ⁻¹-ren-map {τ = τ} {τ' = τ'} (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  _ ,
  ≤-reflexive (trans
                (sym (+-assoc τ' τ τ''))
                (cong (_+ τ'') (+-comm τ' τ))) ,
  Tl-⟨⟩ x

⟨⟩-μ⁻¹-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} =
  ren
    ⟨⟩-μ⁻¹-ren-map
    (≤-reflexive (+-assoc (ctx-time Γ) τ τ'))

-- Monotonicity of ⟨_⟩

⟨⟩-≤-ren-map : ∀ {Γ τ τ'} → τ ≤ τ' → RenMap (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
⟨⟩-≤-ren-map p (Tl-⟨⟩ {τ' = τ'} x) = _ , +-monoˡ-≤ τ' p , Tl-⟨⟩ x

⟨⟩-≤-ren : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
⟨⟩-≤-ren {Γ} p =
  ren
    (⟨⟩-≤-ren-map p)
    (+-monoʳ-≤ (ctx-time Γ) p)

-- Renaming from an equality of contexts

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren refl = id-ren

-- Weakening a context with a ⟨ τ ⟩ renaming

wk-⟨⟩-ren : ∀ {Γ τ} → Ren Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-ren = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren

-- Weakening a ⟨ τ ⟩ modality into a context with at least τ time-passage

wk-⟨⟩-ctx-ren : ∀ {Γ Γ' Γ'' τ}
              → Γ' , Γ'' split Γ
              → τ ≤ ctx-time Γ''
              → Ren (Γ' ⟨ τ ⟩) Γ

wk-⟨⟩-ctx-ren split-[] z≤n = ⟨⟩-η-ren
wk-⟨⟩-ctx-ren (split-∷ p) q = wk-ren ∘ʳ (wk-⟨⟩-ctx-ren p q)
wk-⟨⟩-ctx-ren {τ = τ} (split-⟨⟩ {Γ} {Γ'} {Γ''} {τ = τ'} p) q =
     cong-ren {Γ'' = [] ⟨ τ' ⟩}
       (wk-⟨⟩-ctx-ren {τ = τ ∸ τ'} p
         (≤-trans
           (∸-monoˡ-≤ τ' q)
           (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ'))))
  ∘ʳ ⟨⟩-μ-ren
  ∘ʳ ⟨⟩-≤-ren (n≤n∸m+m τ τ')

-- Splitting a renaming

postulate
  -- TODO: work this out formally; need to calculate the
  -- smallest prefix of Γ' that includes the image of Γ₁

  split-ren : ∀ {Γ Γ' Γ₁ Γ₂ τ}
            → Ren Γ Γ'
            → Γ₁ , Γ₂ split Γ
            → τ ≤ ctx-time Γ₂
            → Σ[ Γ₁' ∈ Ctx ] Σ[ Γ₂' ∈ Ctx ]
                 Ren Γ₁ Γ₁'
               × Γ₁' , Γ₂' split Γ'
               × ctx-time Γ₂ ≤ ctx-time Γ₂'

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename ρ (var x)   = var (proj₂ (proj₂ (ren-map ρ x)))
  V-rename ρ (const c) = const c
  V-rename ρ ⋆         = ⋆
  V-rename ρ (lam M)   = lam (C-rename (cong-ren ρ) M)
  V-rename ρ (box V)   = box (V-rename (cong-ren ρ) V)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename ρ (return V) =
    return (V-rename ρ V)
  C-rename ρ (M ; N) =
    C-rename ρ M ; C-rename (cong-ren ρ) N
  C-rename ρ (V · W) =
    V-rename ρ V · V-rename ρ W
  C-rename ρ (absurd V) =
    absurd (V-rename ρ V)
  C-rename ρ (perform op V M) =
    perform op (V-rename ρ V) (C-rename (cong-ren ρ) M)
  C-rename ρ (handle M `with H `in N) =
    handle C-rename ρ M
    `with (λ op τ'' → C-rename (cong-ren ρ) (H op τ'') )
    `in (C-rename (cong-ren ρ) N)
  C-rename ρ (unbox q r V M) with split-ren ρ q r
  ... | Γ₁' , Γ₂' , ρ' , p' , q' =
    unbox p' (≤-trans r q') (V-rename ρ' V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τ q M) =
    delay τ q (C-rename (cong-ren ρ) M)

