------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

open import Function hiding (const)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language
--open import ContextModality

module Renamings where

-- Variable renamings

-- Note: This allows one to move a variable under more ⟨_⟩s but not vice versa.

Ren : Ctx → Ctx → Set
Ren Γ Γ' = ∀ {A τ} → A ∈[ τ ] Γ → Σ[ τ' ∈ Time ] (τ ≤ τ' × A ∈[ τ' ] Γ')

-- Identity renaming

idʳ : ∀ {Γ} → Ren Γ Γ
idʳ {.(_ ∷ᶜ _)}  Hd        = _ , ≤-refl , Hd
idʳ {.(_ ∷ᶜ _)}  (Tl-∷ᶜ x) = _ , ≤-refl , Tl-∷ᶜ x
idʳ {.(_ ⟨ _ ⟩)} (Tl-⟨⟩ x) = _ , ≤-refl , Tl-⟨⟩ x

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
(ρ' ∘ʳ ρ) {A} {τ} Hd with ρ {A} {τ} Hd
... | τ , p , x with ρ' x
... | τ' , p' , y = τ' , ≤-trans p p' , y
(ρ' ∘ʳ ρ) (Tl-∷ᶜ x) = (ρ' ∘ʳ (ρ ∘ Tl-∷ᶜ)) x
(ρ' ∘ʳ ρ) (Tl-⟨⟩ x) with ρ (Tl-⟨⟩ x)
... | τ , p , y with ρ' y
... | τ' , p' , z = τ' , ≤-trans p p' , z

-- Weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ᶜ A)
wk-ren x = _ , ≤-refl , Tl-∷ᶜ x

-- Exchange renaming

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ᶜ A ∷ᶜ B) (Γ ∷ᶜ B ∷ᶜ A)
exch-ren Hd                = _ , ≤-refl , Tl-∷ᶜ Hd
exch-ren (Tl-∷ᶜ Hd)        = _ , ≤-refl , Hd
exch-ren (Tl-∷ᶜ (Tl-∷ᶜ x)) = _ , ≤-refl , Tl-∷ᶜ (Tl-∷ᶜ x)

-- Contraction renaming

contract-ren : ∀ {Γ A} → Ren (Γ ∷ᶜ A ∷ᶜ A) (Γ ∷ᶜ A)
contract-ren Hd        = _ , ≤-refl , Hd
contract-ren (Tl-∷ᶜ x) = _ , ≤-refl , x

-- Congruence of context renamings

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []} ρ x = ρ x
cong-ren {Γ'' = Γ'' ∷ᶜ A} ρ Hd = _ , ≤-refl , Hd
cong-ren {Γ'' = Γ'' ∷ᶜ A} ρ (Tl-∷ᶜ x) with cong-ren ρ x
... | τ' , p , y = τ' , p , Tl-∷ᶜ y
cong-ren {Γ'' = Γ'' ⟨ τ ⟩} ρ (Tl-⟨⟩ x) with cong-ren ρ x
... | τ' , p , y = τ + τ' , +-monoʳ-≤ τ p , Tl-⟨⟩ y

-- Unit (and its inverse) of ⟨_⟩

⟨⟩-eta-ren : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
⟨⟩-eta-ren (Tl-⟨⟩ x) = _ , ≤-refl , x

⟨⟩-eta⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
⟨⟩-eta⁻¹-ren x = _ , ≤-refl , Tl-⟨⟩ x

-- Multiplication (and its inverse) of ⟨_⟩

⟨⟩-mu-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-mu-ren {τ = τ} {τ' = τ'} (Tl-⟨⟩ {τ' = τ''} x) =
  _ ,
  ≤-reflexive (trans
                (cong (_+ τ'') (+-comm τ τ'))
                (+-assoc τ' τ τ'')) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-mu⁻¹-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-mu⁻¹-ren {τ = τ} {τ' = τ'} (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  _ ,
  ≤-reflexive (trans
                (sym (+-assoc τ' τ τ''))
                (cong (_+ τ'') (+-comm τ' τ))) ,
  Tl-⟨⟩ x

-- Splitting a renaming

n≤n∸m+m : (n m : ℕ) → n ≤ n ∸ m + m
n≤n∸m+m n       zero    = ≤-stepsʳ 0 ≤-refl
n≤n∸m+m zero    (suc m) = z≤n
n≤n∸m+m (suc n) (suc m) =
  ≤-trans
    (+-monoʳ-≤ 1 (n≤n∸m+m n m))
    (≤-reflexive (sym (+-suc (n ∸ m) (m))))

split-ren : ∀ {Γ Γ' Γ₁ Γ₂ τ}
          → Ren Γ Γ'
          → Γ₁ , Γ₂ split Γ
          → τ ≤ ctx-delay Γ₂
          → Σ[ Γ₁' ∈ Ctx ] Σ[ Γ₂' ∈ Ctx ]
             (Ren Γ₁ Γ₁' ×
              Γ₁' , Γ₂' split Γ' ×
              ctx-delay Γ₂ ≤ ctx-delay Γ₂')

split-ren ρ split-[] q = _ , [] , ρ , split-[] , z≤n
split-ren ρ (split-∷ᶜ p) q = split-ren (ρ ∘ Tl-∷ᶜ) p q
split-ren {τ = τ} ρ (split-⟨⟩ {τ = τ'} p) q = {!!}
{-
  with split-ren
         {τ = τ ∸ τ'}
         (λ x → let (τ'' , r , y) = ρ (Tl-⟨⟩ x) in
                _ , ≤-trans (≤-stepsˡ τ' ≤-refl) r , y)
         p
         {!!}
... | Γ₁' , Γ₂' , ρ' , p' , q' = 
  Γ₁' , Γ₂' ⟨ τ' ⟩ , ρ' , {!!} , {!!}
-}

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
  C-rename ρ (coerce q M)     = coerce q (C-rename ρ M)

{-
-- Splitting a renaming

split-ren : ∀ {Γ Γ' Γ₁ Γ₂ τ τ'}
          → Ren Γ Γ'
          → Γ₁ ⟨ τ' ⟩ , Γ₂ split Γ
          → τ ≤ τ' + ctx-delay Γ₂
          → Σ[ Γ₁' ∈ Ctx ] Σ[ Γ₂' ∈ Ctx ]
             (Ren Γ₁ Γ₁' ×
              Γ₁' ⟨ τ' ⟩ , Γ₂' split Γ' ×
              τ ≤ τ' + ctx-delay Γ₂')
              
split-ren (wk ρ) split-[] q with split-ren ρ split-[] q
... | Γ₁' , Γ₂' , ρ' , p' , q' = Γ₁' , Γ₂' ∷ᶜ _ , ρ' , split-∷ᶜ p' , q'
split-ren (⟨⟩ ρ) split-[] q =
  _ , [] , ρ , ≡-split refl , q
split-ren (wk ρ) (split-∷ᶜ p) q with split-ren ρ (split-∷ᶜ p) q
... | Γ₁' , Γ₂' , ρ' , p' , q' = Γ₁' , Γ₂' ∷ᶜ _ , ρ' , split-∷ᶜ p' , q'
split-ren (ext ρ x) (split-∷ᶜ p) q = split-ren ρ p q
split-ren (wk ρ) (split-⟨⟩ p) q with split-ren ρ (split-⟨⟩ p) q
... | Γ₁' , Γ₂' , ρ' , p' , q' = Γ₁' , Γ₂' ∷ᶜ _ , ρ' , split-∷ᶜ p' , q'
split-ren {τ = τ} {τ' = τ'} (⟨⟩ ρ) (split-⟨⟩ {Γ' = Γ'} {τ = τ''} p) q
  with split-ren {τ = τ ∸ τ'' } ρ p 
         (≤-trans     -- τ ≤ τ' + (ctx-delay Γ' + τ'') implies τ ∸ τ'' ≤ τ' + ctx-delay Γ'
           (≤-trans
             (≤-trans
               (≤-trans
                 (∸-monoˡ-≤ τ'' q)
                 (≤-reflexive (+-∸-assoc τ' {ctx-delay Γ' + τ''} {τ''} (≤-stepsˡ (ctx-delay Γ') ≤-refl))))
               (+-monoʳ-≤ τ' (≤-reflexive (+-∸-assoc (ctx-delay Γ') (≤-refl {τ''})))))
             (≤-reflexive (sym (+-assoc τ' (ctx-delay Γ') (τ'' ∸ τ'')))))
           (≤-reflexive (trans (cong (τ' + ctx-delay Γ' +_) (n∸n≡0 τ'')) (+-identityʳ (τ' + ctx-delay Γ')))))
... | Γ₁' , Γ₂' , ρ' , p' , q' =
  Γ₁' , Γ₂' ⟨ τ'' ⟩ , ρ' , split-⟨⟩ p' ,
    ≤-trans
      (≤-trans (n≤n∸m+m τ τ'') (+-monoˡ-≤ τ'' q'))
      (≤-reflexive (+-assoc τ' (ctx-delay Γ₂') τ''))
-}
