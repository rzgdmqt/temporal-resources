------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

open import Function hiding (const)

open import Data.Bool hiding (_≤_;_≤?_)
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary.Definitions

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Util.Equality
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

split-ren (ρ' ∘ʳ ρ) p q with split-ren ρ p q
... | Γ₁' , Γ₂' , ρ'' , p' , q' with split-ren ρ' p' q'
... | Γ₁'' , Γ₂'' , ρ''' , p'' , q'' =
  Γ₁'' , Γ₂'' , ρ''' ∘ʳ ρ'' , p'' , q''

split-ren wk-ren p q =
  _ , _ , id-ren , split-∷ p , q

split-ren (var-ren x) split-[] q =
  _ , _ , var-ren x , split-[] , q
split-ren (var-ren x) (split-∷ p) q =
  _ , _ , id-ren , p , q

split-ren ⟨⟩-η-ren split-[] q =
  _ , _ , ⟨⟩-η-ren , split-[] , q
split-ren ⟨⟩-η-ren (split-⟨⟩ {Γ' = Γ'} p) q =
  _ , _ , id-ren , p , ≤-trans q (≤-reflexive (+-identityʳ (ctx-time Γ')))

split-ren ⟨⟩-η⁻¹-ren p q =
  _ , _ , id-ren , split-⟨⟩ p , ≤-stepsʳ 0 q

split-ren ⟨⟩-μ-ren split-[] q =
  _ , _ , ⟨⟩-μ-ren , split-[] , q
split-ren (⟨⟩-μ-ren {τ = τ} {τ' = τ'}) (split-⟨⟩ {Γ' = Γ'} p) q =
  _ , _ , id-ren , split-⟨⟩ (split-⟨⟩ p) ,
  ≤-trans q (≤-reflexive (sym (+-assoc (ctx-time Γ') τ τ')))

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
split-ren {τ = τ} (cong-⟨⟩-ren {τ = τ'} ρ) (split-⟨⟩ {Γ' = Γ'} p) q
  with split-ren {τ = τ ∸ τ'} ρ p
         (≤-trans (∸-monoˡ-≤ τ' q) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
... | Γ₁ , Γ₂ , ρ' , p' , q' =
  _ , _ , ρ' , split-⟨⟩ p' ,
  ≤-trans
    (n≤n∸m+m τ τ')
    (+-monoˡ-≤ τ' q')

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
  C-rename ρ (handle M `with H `in N) =
    handle C-rename ρ M
    `with (λ op τ'' → C-rename (cong-ren ρ) (H op τ'') )
    `in (C-rename (cong-ren ρ) N)
  C-rename ρ (unbox q r V M) with split-ren ρ q r
  ... | Γ₁' , Γ₂' , ρ' , p' , q' =
    unbox p' q' (V-rename ρ' V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τs q M)      = delay τs q (C-rename (cong-ren ρ) M)
