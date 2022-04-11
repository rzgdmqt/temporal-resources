------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

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
... | τ , p , x = {!ρ' x!}
(ρ' ∘ʳ ρ) (Tl-∷ᶜ x) = {!!}
(ρ' ∘ʳ ρ) (Tl-⟨⟩ x) = {!!}



{-
-- Variable renamings

-- Note: do not include the unit, multiplication, and monotonicity
-- laws of ⟨_⟩---these are proved separately in ContextModality.agda.

data Ren : Ctx → Ctx → Set where
  ∅   : ∀ {Γ} → Ren [] Γ
  wk  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren Γ (Γ' ∷ᶜ A)
  ext : ∀ {Γ Γ' A} → Ren Γ Γ' → A ∈ Γ' → Ren (Γ ∷ᶜ A) Γ'
  ⟨⟩  : ∀ {Γ Γ' τ } → Ren Γ Γ' → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)

-- Renaming a variable

var-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → A ∈ Γ
           ------------
           → A ∈ Γ'

var-rename (wk ρ)    Hd     = Tl (var-rename ρ Hd)
var-rename (ext ρ x) Hd     = x
var-rename (wk ρ)    (Tl x) = Tl (var-rename ρ (Tl x))
var-rename (ext ρ _) (Tl x) = var-rename ρ x

-- Identity renaming

idʳ : ∀ {Γ} → Ren Γ Γ
idʳ {[]}      = ∅
idʳ {Γ ∷ᶜ A}  = ext (wk idʳ) Hd
idʳ {Γ ⟨ τ ⟩} = ⟨⟩ idʳ

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
ρ'       ∘ʳ ∅          = ∅
wk ρ'    ∘ʳ wk ρ       = wk (ρ' ∘ʳ wk ρ)
ext ρ' x ∘ʳ wk ρ       = ρ' ∘ʳ ρ
ρ'       ∘ʳ ext ρ x    = ext (ρ' ∘ʳ ρ) (var-rename ρ' x)
wk ρ'    ∘ʳ ⟨⟩ ρ       = wk (ρ' ∘ʳ ⟨⟩ ρ)
⟨⟩ ρ'    ∘ʳ ⟨⟩ ρ       = ⟨⟩ (ρ' ∘ʳ ρ) 

-- Weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ᶜ A)
wk-ren = wk idʳ

-- Exchange renaming

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ᶜ A ∷ᶜ B) (Γ ∷ᶜ B ∷ᶜ A)
exch-ren {Γ} = ext (ext (wk (wk idʳ)) Hd) (Tl Hd)

-- Contraction renaming

contract-ren : ∀ {Γ A} → Ren (Γ ∷ᶜ A ∷ᶜ A) (Γ ∷ᶜ A)
contract-ren = ext idʳ Hd

-- Congruence of context renamings

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []}        ρ = ρ
cong-ren {Γ'' = Γ'' ∷ᶜ A}  ρ = ext (wk (cong-ren ρ)) Hd
cong-ren {Γ'' = Γ'' ⟨ τ ⟩} ρ = ⟨⟩ (cong-ren ρ)

-- Splitting a renaming

n≤n∸m+m : (n m : ℕ) → n ≤ n ∸ m + m
n≤n∸m+m n       zero    = ≤-stepsʳ 0 ≤-refl
n≤n∸m+m zero    (suc m) = z≤n
n≤n∸m+m (suc n) (suc m) =
  ≤-trans
    (+-monoʳ-≤ 1 (n≤n∸m+m n m))
    (≤-reflexive (sym (+-suc (n ∸ m) (m))))

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

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename ρ (var x)   = var (var-rename ρ x)
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
  C-rename ρ (unbox q r V M)  = unbox
                                  (proj₁ (proj₂ (proj₂ (proj₂ (split-ren ρ q r)))))
                                  (proj₂ (proj₂ (proj₂ (proj₂ (split-ren ρ q r)))))
                                  (V-rename (proj₁ (proj₂ (proj₂ (split-ren ρ q r)))) V)
                                  (C-rename (cong-ren ρ) M)
  C-rename ρ (coerce q M)     = coerce q (C-rename ρ M)
  
-}
