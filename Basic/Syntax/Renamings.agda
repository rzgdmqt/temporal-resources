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

data Ren : Ctx → Ctx → Set where
  -- identity renaming on empty contexts
  []-ren      : Ren [] []
  -- composition
  _∘ʳ_        : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
  -- weakening renaming
  wk-ren      : ∀ {Γ A} → Ren Γ (Γ ∷ A)
  -- variable renaming
  var-ren     : ∀ {Γ A τ} → A ∈[ τ ] Γ → Ren (Γ ∷ A) Γ
  -- ⟨⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
  ⟨⟩-≤-ren    : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
  -- congruences
  cong-∷-ren  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)

infixr 20 _∘ʳ_

-- Identity renaming

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {Γ = []}      = []-ren
id-ren {Γ = Γ ∷ A}   = cong-∷-ren id-ren
id-ren {Γ = Γ ⟨ τ ⟩} = cong-⟨⟩-ren id-ren

-- Extending a renaming with a variable

extend-ren : ∀ {Γ Γ' A τ} → Ren Γ Γ' → A ∈[ τ ] Γ' → Ren (Γ ∷ A) Γ'
extend-ren ρ x = var-ren x ∘ʳ cong-∷-ren ρ

-- Congruence of renamings

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []} ρ = ρ
cong-ren {Γ'' = Γ'' ∷ A} ρ = cong-∷-ren (cong-ren ρ)
cong-ren {Γ'' = Γ'' ⟨ τ ⟩} ρ = cong-⟨⟩-ren (cong-ren ρ)

-- Weakening by a modality renaming

wk-⟨⟩-ren : ∀ {Γ τ} → Ren Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-ren = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren

-- Weakening by a context renaming

wk-ctx-ren : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-ren {Γ' = []} = id-ren
wk-ctx-ren {Γ' = Γ' ∷ A} = wk-ren ∘ʳ wk-ctx-ren
wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} = wk-⟨⟩-ren ∘ʳ wk-ctx-ren

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

-- Exchange renamings

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = extend-ren (extend-ren wk-ctx-ren Hd) (Tl-∷ Hd)

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren {A = A} {τ = τ} =
  var-ren (Tl-⟨⟩ Hd) ∘ʳ cong-ren {Γ'' = [] ⟨ _ ⟩ ∷ _} wk-ren

exch-⟨⟩-⟨⟩-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ' ⟩ ⟨ τ ⟩)
exch-⟨⟩-⟨⟩-ren {τ = τ} {τ' = τ'} =
  ⟨⟩-μ-ren ∘ʳ ⟨⟩-≤-ren (≤-reflexive (+-comm τ τ')) ∘ʳ ⟨⟩-μ⁻¹-ren

-- Contraction renaming

contract-ren : ∀ {Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren = var-ren Hd

-- Renaming from an equality of contexts

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren refl = id-ren

-- Splitting a renaming

--postulate
  -- TODO: work this out formally; need to calculate the
  -- smallest prefix of Γ' that includes the image of Γ₁

split-ren : ∀ {Γ Γ' Γ₁ Γ₂ τ}
          → Ren Γ Γ'
          → Γ₁ , Γ₂ split Γ
          → τ ≤ ctx-time Γ₂
          → Σ[ Γ₁' ∈ Ctx ] Σ[ Γ₂' ∈ Ctx ]
               Ren Γ₁ Γ₁'
             × Γ₁' , Γ₂' split Γ'
             × τ ≤ ctx-time Γ₂'

split-ren []-ren split-[] q =
  [] , [] , []-ren , split-[] , q

split-ren (ρ' ∘ʳ ρ) p q = {!!}

split-ren wk-ren p q =
  _ , _ , id-ren , split-∷ p , q

split-ren (var-ren x) split-[] q =
  _ , _ , var-ren x , split-[] , {!!}
split-ren (var-ren x) (split-∷ p) q =
  _ , _ , id-ren , p , q

split-ren ⟨⟩-η-ren split-[] q =
  _ , _ , ⟨⟩-η-ren , split-[] , {!!}
split-ren ⟨⟩-η-ren (split-⟨⟩ p) q =
  _ , _ , id-ren , p , {!!}

split-ren ⟨⟩-η⁻¹-ren p q =
  _ , _ , id-ren , split-⟨⟩ p , {!!}

split-ren ⟨⟩-μ-ren split-[] q =
  _ , _ , ⟨⟩-μ-ren , split-[] , {!!}
split-ren (⟨⟩-μ-ren {τ = τ} {τ' = τ'}) (split-⟨⟩ {Γ' = Γ'} p) q =
  _ , _ , id-ren , split-⟨⟩ (split-⟨⟩ p) ,
  {!!}

split-ren ⟨⟩-μ⁻¹-ren split-[] q = _ , _ , ⟨⟩-μ⁻¹-ren , split-[] , q
split-ren ⟨⟩-μ⁻¹-ren (split-⟨⟩ split-[]) q = {!!} , {!!} , {!!} , {!!} , {!!} -- TODO: this case is problematic
split-ren ⟨⟩-μ⁻¹-ren (split-⟨⟩ (split-⟨⟩ p)) q =
  _ , _ , id-ren , split-⟨⟩ p ,
  ≤-reflexive (+-assoc {!!} {!!} {!!})

split-ren (⟨⟩-≤-ren r) split-[] q =
  _ , _ , ⟨⟩-≤-ren r , split-[] , q
split-ren (⟨⟩-≤-ren r) (split-⟨⟩ p) q =
  _ , _ , id-ren , split-⟨⟩ p , ≤-trans q (+-monoʳ-≤ _ r)

split-ren (cong-∷-ren ρ) split-[] q =
  _ , _ , cong-∷-ren ρ , split-[] , q
split-ren (cong-∷-ren ρ) (split-∷ p) q with split-ren ρ p q
... | Γ₁ , Γ₂ , ρ' , p' , q' =
  _ , _ , ρ' , split-∷ p' , q'

split-ren (cong-⟨⟩-ren ρ) split-[] q =
  _ , _ , cong-⟨⟩-ren ρ , split-[] , q
split-ren {τ = τ} (cong-⟨⟩-ren {τ = τ'} ρ) (split-⟨⟩ p) q with split-ren {τ = τ ∸ τ'} ρ p {!!}
... | Γ₁ , Γ₂ , ρ' , p' , q' =
  _ , _ , ρ' , split-⟨⟩ p' , {!!}

-- Action of renamings on variables (showing that reamings
-- allow one to move any variable under more ⟨_⟩ modalities)

var-rename : ∀ {Γ Γ'}
           → Ren Γ Γ'
           →  ∀ {A τ} → A ∈[ τ ] Γ → Σ[ τ' ∈ Time ] (τ ≤ τ' × A ∈[ τ' ] Γ')

var-rename (ρ' ∘ʳ ρ) x with (var-rename ρ) x
... | τ , p , y with (var-rename ρ') y
... | τ' , p' , y' =
  _ , ≤-trans p p' , y'
var-rename wk-ren x =
  _ , ≤-refl , Tl-∷ x
var-rename (var-ren y) Hd =
  _ , z≤n , y
var-rename (var-ren y) (Tl-∷ x) =
  _ , ≤-refl , x
var-rename ⟨⟩-η-ren (Tl-⟨⟩ x) =
  _ , ≤-refl , x
var-rename ⟨⟩-η⁻¹-ren x =
  _ , ≤-refl , Tl-⟨⟩ x
var-rename (⟨⟩-μ-ren {τ = τ} {τ' = τ'}) (Tl-⟨⟩ {τ' = τ''} x) =
  _ ,
  ≤-reflexive (trans
                (cong (_+ τ'') (+-comm τ τ'))
                (+-assoc τ' τ τ'')) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)
var-rename (⟨⟩-μ⁻¹-ren {τ = τ} {τ' = τ'}) (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  _ ,
  ≤-reflexive (trans
                (sym (+-assoc τ' τ τ''))
                (cong (_+ τ'') (+-comm τ' τ))) ,
  Tl-⟨⟩ x
var-rename (⟨⟩-≤-ren p) (Tl-⟨⟩ x) =
  _ , +-monoˡ-≤ _ p , Tl-⟨⟩ x
var-rename (cong-∷-ren ρ) Hd =
  _ , z≤n , Hd
var-rename (cong-∷-ren ρ) (Tl-∷ x) with var-rename ρ x
... | τ , p , y =
  _ , p , Tl-∷ y
var-rename (cong-⟨⟩-ren ρ) (Tl-⟨⟩ x) with var-rename ρ x
... | τ , p , y =
  _ , +-monoʳ-≤ _ p , Tl-⟨⟩ y

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename ρ (var x)   = var (proj₂ (proj₂ (var-rename ρ x)))
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
    unbox p' q' (V-rename ρ' V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τ q M)      = delay τ q (C-rename (cong-ren ρ) M)











{-

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


-- Calculating the image of a renaming

-- TODO: in an attempt to construct splittings of renamings below
{-
ctx-length : Ctx → ℕ
ctx-length [] = 0
ctx-length (Γ ∷ A) = ctx-length Γ + 1
ctx-length (Γ ⟨ τ ⟩) = ctx-length Γ + 1

ren-image : ∀ {Γ Γ'}
          → Ren Γ Γ'
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Ren Γ Γ₁ × Γ₁ , Γ₂ split Γ')

ren-image {[]} {Γ'} ρ = [] , Γ' , idʳ , ≡-split ++ᶜ-identityˡ
ren-image {Γ ∷ A} ρ with ren-image {Γ} (ρ ∘ʳ wk-ren) | var-split (proj₂ (proj₂ (ρ Hd)))
... | Γ₁ , Γ₂ , ρ' , p | Γ₁' , Γ₂' , q , r with ctx-length Γ₁ <ᵇ ctx-length Γ₁'
... | false = Γ₁ , Γ₂ , extend-ren ρ' {!!} , p
... | true  = Γ₁' ∷ A , Γ₂' , extend-ren {!!} {!!} , q
ren-image {Γ ⟨ τ ⟩} ρ with ren-image {Γ} (ρ ∘ʳ ⟨⟩-mon-ren z≤n ∘ʳ ⟨⟩-eta⁻¹-ren)
... | Γ₁ , Γ₂ , ρ' , p = {!!}
-}


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


{-
split-ren ρ split-[] q = _ , [] , ρ , split-[] , z≤n
split-ren ρ (split-∷ᶜ p) q = split-ren (ρ ∘ Tl-∷ᶜ) p q
split-ren {τ = τ} ρ (split-⟨⟩ {τ = τ'} p) q 
  with split-ren
         {τ = τ ∸ τ'}
         (λ x → let (τ'' , r , y) = ρ (Tl-⟨⟩ x) in
                _ , ≤-trans (≤-stepsˡ τ' ≤-refl) r , y)
         p
         {!!}
... | Γ₁' , Γ₂' , ρ' , p' , q' = 
  Γ₁' , {!!} , ρ' , {!!} , {!!}
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
  C-rename ρ (delay τ q M)      = delay τ q (C-rename (cong-ren ρ) M)

-}
