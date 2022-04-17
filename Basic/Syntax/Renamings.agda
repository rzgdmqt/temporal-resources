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

-- Note: This allows one to move a variable under more ⟨_⟩s but not vice versa.

Ren : Ctx → Ctx → Set
Ren Γ Γ' = ∀ {A τ} → A ∈[ τ ] Γ → Σ[ τ' ∈ Time ] (τ ≤ τ' × A ∈[ τ' ] Γ')

-- Identity renaming

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {.(_ ∷ _)}  Hd         = _ , ≤-refl , Hd
id-ren {.(_ ∷ _)}  (Tl-∷ x)   = _ , ≤-refl , Tl-∷ x
id-ren {.(_ ⟨ _ ⟩)} (Tl-⟨⟩ x) = _ , ≤-refl , Tl-⟨⟩ x

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
(ρ' ∘ʳ ρ) {A} {τ} Hd with ρ {A} {τ} Hd
... | τ , p , x with ρ' x
... | τ' , p' , y = τ' , ≤-trans p p' , y
(ρ' ∘ʳ ρ) (Tl-∷ x) = (ρ' ∘ʳ (ρ ∘ Tl-∷)) x
(ρ' ∘ʳ ρ) (Tl-⟨⟩ x) with ρ (Tl-⟨⟩ x)
... | τ , p , y with ρ' y
... | τ' , p' , z = τ' , ≤-trans p p' , z

infixr 20 _∘ʳ_

-- Variable weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ A)
wk-ren x = _ , ≤-refl , Tl-∷ x

wk-ctx-ren : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-ren {Γ' = []}       x = _ , ≤-refl , x
wk-ctx-ren {Γ' = Γ' ∷ A}   x with wk-ctx-ren {Γ' = Γ'} x
... | τ' , p , y = τ' , p , Tl-∷ y
wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} x with wk-ctx-ren {Γ' = Γ'} x
... | τ' , p , y = τ + τ' , ≤-stepsˡ τ p , Tl-⟨⟩ y

-- Exchange renamings

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren Hd              = _ , ≤-refl , Tl-∷ Hd
exch-ren (Tl-∷ Hd)       = _ , ≤-refl , Hd
exch-ren (Tl-∷ (Tl-∷ x)) = _ , ≤-refl , Tl-∷ (Tl-∷ x)

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren Hd               = _ , z≤n , Tl-⟨⟩ Hd
exch-⟨⟩-var-ren (Tl-∷ (Tl-⟨⟩ x)) = _ , ≤-refl , Tl-⟨⟩ (Tl-∷ x)

exch-⟨⟩-⟨⟩-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ' ⟩ ⟨ τ ⟩)
exch-⟨⟩-⟨⟩-ren {τ = τ} {τ' = τ'} (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  τ + (τ' + τ'') ,
  ≤-reflexive
    (trans
      (sym (+-assoc τ' τ τ''))
      (trans
        (cong (_+ τ'') (+-comm τ' τ))
        (+-assoc τ τ' τ''))) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

-- Contraction renaming

contract-ren : ∀ {Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren Hd       = _ , ≤-refl , Hd
contract-ren (Tl-∷ x) = _ , ≤-refl , x

-- Extending a renaming

extend-ren : ∀ {Γ Γ' A τ} → Ren Γ Γ' → A ∈[ τ ] Γ' → Ren (Γ ∷ A) Γ'
extend-ren ρ x Hd       = _ , z≤n , x
extend-ren ρ x (Tl-∷ y) = ρ y

-- Congruence of context renamings

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []} ρ x = ρ x
cong-ren {Γ'' = Γ'' ∷ A} ρ Hd = _ , ≤-refl , Hd
cong-ren {Γ'' = Γ'' ∷ A} ρ (Tl-∷ x) with cong-ren ρ x
... | τ' , p , y = τ' , p , Tl-∷ y
cong-ren {Γ'' = Γ'' ⟨ τ ⟩} ρ (Tl-⟨⟩ x) with cong-ren ρ x
... | τ' , p , y = τ + τ' , +-monoʳ-≤ τ p , Tl-⟨⟩ y

-- Unit (and its inverse) of ⟨_⟩

⟨⟩-η-ren : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
⟨⟩-η-ren (Tl-⟨⟩ x) = _ , ≤-refl , x

⟨⟩-η⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
⟨⟩-η⁻¹-ren x = _ , ≤-refl , Tl-⟨⟩ x

-- Multiplication (and its inverse) of ⟨_⟩

⟨⟩-μ-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-μ-ren {τ = τ} {τ' = τ'} (Tl-⟨⟩ {τ' = τ''} x) =
  _ ,
  ≤-reflexive (trans
                (cong (_+ τ'') (+-comm τ τ'))
                (+-assoc τ' τ τ'')) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-μ⁻¹-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-μ⁻¹-ren {τ = τ} {τ' = τ'} (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  _ ,
  ≤-reflexive (trans
                (sym (+-assoc τ' τ τ''))
                (cong (_+ τ'') (+-comm τ' τ))) ,
  Tl-⟨⟩ x

-- Monotonicity of ⟨_⟩

⟨⟩-≤-ren : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
⟨⟩-≤-ren p (Tl-⟨⟩ {τ' = τ'} x) = _ , +-monoˡ-≤ τ' p , Tl-⟨⟩ x

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

  V-rename ρ (var x)   = var (proj₂ (proj₂ (ρ x)))
  V-rename ρ (const c) = const c
  V-rename ρ ⋆         = ⋆
  V-rename ρ (lam M)   = lam (C-rename (cong-ren ρ) M)
  V-rename ρ (box V)   = box (V-rename (cong-ren ρ) V)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename ρ (return V)       = return (V-rename ρ V)
  C-rename ρ (M ; N)          = C-rename ρ M ; C-rename (cong-ren ρ) N
  C-rename ρ (V · W)          = V-rename ρ V · V-rename ρ W
  C-rename ρ (absurd V)       = absurd (V-rename ρ V)
  C-rename ρ (perform op V M) = perform op (V-rename ρ V) (C-rename (cong-ren ρ) M)
  C-rename ρ (unbox q r V M)  with split-ren ρ q r
  ... | Γ₁' , Γ₂' , ρ' , p' , q' =
    unbox p' (≤-trans r q') (V-rename ρ' V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τ q M)    = delay τ q (C-rename (cong-ren ρ) M)

