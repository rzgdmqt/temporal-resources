------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

open import Function hiding (const)

open import Data.Bool hiding (_≤_;_≤?_)
open import Data.Empty
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

-- Variable renamings (as the least relation closed under
-- identities, composition, ordinary variable renamings,
-- and graded monad operations for the ⟨_⟩ modality).

data Ren : Ctx → Ctx → Set where
  -- identity renaming
  id-ren      : ∀ {Γ} → Ren Γ Γ
  -- composition of renamings
  _∘ʳ_        : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
  -- weakening renaming
  wk-ren      : ∀ {Γ A} → Ren Γ (Γ ∷ A)
  -- variable renaming
  var-ren     : ∀ {Γ A τ} → A ∈[ τ ] Γ → Ren (Γ ∷ A) Γ
  -- graded monad renamings for ⟨⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
  ⟨⟩-≤-ren    : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
  -- congruence renamings
  cong-∷-ren  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)

infixr 20 _∘ʳ_

-- Extending a renaming with a variable

extend-ren : ∀ {Γ Γ' A τ} → Ren Γ Γ' → A ∈[ τ ] Γ' → Ren (Γ ∷ A) Γ'
extend-ren ρ x = var-ren x ∘ʳ cong-∷-ren ρ

-- Congruence of renamings

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []} ρ        = ρ
cong-ren {Γ'' = Γ'' ∷ A} ρ   = cong-∷-ren (cong-ren ρ)
cong-ren {Γ'' = Γ'' ⟨ τ ⟩} ρ = cong-⟨⟩-ren (cong-ren ρ)

-- Weakening by a modality renaming

wk-⟨⟩-ren : ∀ {Γ τ} → Ren Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-ren = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren

-- Weakening by a context renaming

wk-ctx-ren : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-ren {Γ' = []}       = id-ren
wk-ctx-ren {Γ' = Γ' ∷ A}   = wk-ren ∘ʳ wk-ctx-ren
wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} = wk-⟨⟩-ren ∘ʳ wk-ctx-ren

-- Weakening a ⟨ τ ⟩ modality into a context with at least τ time-passage

wk-⟨⟩-ctx-ren : ∀ {Γ Γ' Γ'' τ}
              → Γ' , Γ'' split Γ
              → τ ≤ ctx-time Γ''
              → Ren (Γ' ⟨ τ ⟩) Γ

wk-⟨⟩-ctx-ren split-[] z≤n = ⟨⟩-η-ren
wk-⟨⟩-ctx-ren (split-∷ p) q =
     wk-ren
  ∘ʳ (wk-⟨⟩-ctx-ren p q)
wk-⟨⟩-ctx-ren {τ = τ} (split-⟨⟩ {Γ} {Γ'} {Γ''} {τ = τ'} p) q =
     cong-ren {Γ'' = [] ⟨ τ' ⟩}
       (wk-⟨⟩-ctx-ren {τ = τ ∸ τ'} p
         (≤-trans
           (∸-monoˡ-≤ τ' q)
           (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ'))))
  ∘ʳ ⟨⟩-μ-ren
  ∘ʳ ⟨⟩-≤-ren (n≤n∸m+m τ τ')

-- Weakening a ⟨ tctx-time τs ⟩ modality into a temporal context

wk-⟨⟩-tctx-ren : ∀ {Γ} (τs : TCtx) → Ren (Γ ⟨ tctx-time τs ⟩) (Γ ++ᶜ tctx-ctx τs)
wk-⟨⟩-tctx-ren ⦉ τ ⦊ =
  id-ren
wk-⟨⟩-tctx-ren (τs ⟨ τ ⟩) =
     cong-⟨⟩-ren (wk-⟨⟩-tctx-ren τs)
  ∘ʳ ⟨⟩-μ-ren

-- Exchange renamings

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = extend-ren (extend-ren wk-ctx-ren Hd) (Tl-∷ Hd)

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren {A = A} {τ = τ} =
     var-ren (Tl-⟨⟩ Hd)
  ∘ʳ cong-ren {Γ'' = [] ⟨ _ ⟩ ∷ _} wk-ren

exch-⟨⟩-tctx-var-ren : ∀ {Γ A} → (τs : TCtx)
                     → Ren (Γ ++ᶜ tctx-ctx τs ∷ A) ((Γ ∷ A) ++ᶜ tctx-ctx τs)
exch-⟨⟩-tctx-var-ren ⦉ τ ⦊ =
  exch-⟨⟩-var-ren
exch-⟨⟩-tctx-var-ren (τs ⟨ τ ⟩) =
     cong-⟨⟩-ren (exch-⟨⟩-tctx-var-ren τs)
  ∘ʳ exch-⟨⟩-var-ren

-- Contraction renaming

contract-ren : ∀ {Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren = var-ren Hd

-- Renaming from an equality of contexts

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren refl = id-ren

-- Weakening renaming for the time-travelling operation on contexts

-ᶜ-wk-ren : ∀ {Γ} → (τ : Time) → Ren (Γ -ᶜ τ) Γ
-ᶜ-wk-ren {Γ} zero =
  id-ren
-ᶜ-wk-ren {[]} (suc τ) =
  id-ren
-ᶜ-wk-ren {Γ ∷ A} (suc τ) =
  wk-ren ∘ʳ -ᶜ-wk-ren {Γ} (suc τ)
-ᶜ-wk-ren {Γ ⟨ τ' ⟩} (suc τ) with suc τ ≤? τ'
... | yes p = ⟨⟩-≤-ren (m∸n≤m τ' (suc τ))
... | no ¬p =
  wk-⟨⟩-ren ∘ʳ -ᶜ-wk-ren (suc τ ∸ τ')

-- Monotonicity renaming for the time-travelling operation on contexts

-ᶜ-≤-ren : ∀ {Γ τ₁ τ₂} → τ₁ ≤ τ₂ → Ren (Γ -ᶜ τ₂) (Γ -ᶜ τ₁)
-ᶜ-≤-ren {Γ} {zero} {zero} p =
  id-ren
-ᶜ-≤-ren {Γ} {zero} {suc τ₂} p =
  -ᶜ-wk-ren (suc τ₂)
-ᶜ-≤-ren {[]} {suc τ₁} {suc τ₂} p =
  id-ren
-ᶜ-≤-ren {Γ ∷ A} {suc τ₁} {suc τ₂} p =
  -ᶜ-≤-ren {Γ} p
-ᶜ-≤-ren {Γ ⟨ τ ⟩} {suc τ₁} {suc τ₂} p with suc τ₁ ≤? τ | suc τ₂ ≤? τ
... | yes q | yes r =
  ⟨⟩-≤-ren (∸-monoʳ-≤ τ p)
... | yes q | no ¬r =
     wk-⟨⟩-ren
  ∘ʳ -ᶜ-wk-ren (suc τ₂ ∸ τ)
... | no ¬q | yes r =
  ⊥-elim (¬q (≤-trans p r))
... | no ¬q | no ¬r =
  -ᶜ-≤-ren {Γ} {suc τ₁ ∸ τ} {suc τ₂ ∸ τ} (∸-monoˡ-≤ τ p)

-- Time-travelling operation on renamings

_-ʳ_ : ∀ {Γ Γ'} → Ren Γ Γ' → (τ : Time) → Ren (Γ -ᶜ τ) (Γ' -ᶜ τ)
ρ             -ʳ zero  = ρ
id-ren        -ʳ suc τ = id-ren
(ρ' ∘ʳ ρ)     -ʳ suc τ = (ρ' -ʳ suc τ) ∘ʳ (ρ -ʳ suc τ)
wk-ren        -ʳ suc τ = id-ren
var-ren x     -ʳ suc τ = id-ren
⟨⟩-η-ren      -ʳ suc τ = id-ren
⟨⟩-η⁻¹-ren    -ʳ suc τ = id-ren

⟨⟩-μ-ren {Γ} {τ₁} {τ₂} -ʳ suc τ with suc τ ≤? τ₁ + τ₂ | suc τ ≤? τ₂
⟨⟩-μ-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | yes p | yes q =
  ⟨⟩-μ-ren ∘ʳ ⟨⟩-≤-ren (≤-reflexive (+-∸-assoc τ₁ q))
⟨⟩-μ-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | yes p | no ¬q with suc τ ∸ τ₂ | inspect (λ (τ , τ₂) → suc τ ∸ τ₂) (τ , τ₂)
... | zero  | [| eq |] = ⊥-elim (¬q (m∸n≡0⇒m≤n eq))
... | suc r | [| eq |] with suc r ≤? τ₁
... | yes s rewrite sym eq =
  ⟨⟩-≤-ren (≤-reflexive (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m ¬q s))
... | no ¬s rewrite sym eq =
  ⊥-elim (¬s (≤-trans (∸-monoˡ-≤ τ₂ p) (≤-reflexive (m+n∸n≡m τ₁ τ₂))))
⟨⟩-μ-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | no ¬p | yes q =
  ⊥-elim (n≤k⇒¬n≤m+k-contradiction q ¬p)
⟨⟩-μ-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | no ¬p | no ¬q with suc τ ∸ τ₂ | inspect (λ (τ , τ₂) → suc τ ∸ τ₂) (τ , τ₂)
... | zero  | [| eq |] =
  ⊥-elim (¬q (m∸n≡0⇒m≤n eq))
... | suc r | [| eq |] with suc r ≤? τ₁
... | yes s rewrite sym eq =
  ⊥-elim (¬p (≤-trans (n≤n∸m+m (suc τ) τ₂) (+-monoˡ-≤ τ₂ s)))
... | no ¬s rewrite sym eq =
  eq-ren (cong (Γ -ᶜ_) (trans (cong (suc τ ∸_) (+-comm τ₁ τ₂)) (sym (∸-+-assoc (suc τ) τ₂ τ₁))))

⟨⟩-μ⁻¹-ren {Γ} {τ₁} {τ₂} -ʳ suc τ with suc τ ≤? τ₁ + τ₂ | suc τ ≤? τ₂
⟨⟩-μ⁻¹-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | yes p | yes q =
  ⟨⟩-≤-ren (≤-reflexive (sym (+-∸-assoc τ₁ q))) ∘ʳ ⟨⟩-μ⁻¹-ren
⟨⟩-μ⁻¹-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | yes p | no ¬q with suc τ ∸ τ₂ | inspect (λ (τ , τ₂) → suc τ ∸ τ₂) (τ , τ₂)
... | zero  | [| eq |] = ⊥-elim (¬q (m∸n≡0⇒m≤n eq))
... | suc r | [| eq |] with suc r ≤? τ₁
... | yes s rewrite sym eq =
  ⟨⟩-≤-ren (≤-reflexive (sym (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m ¬q s)))
... | no ¬s rewrite sym eq = ⊥-elim (¬s (≤-trans (∸-monoˡ-≤ τ₂ p) (≤-reflexive (m+n∸n≡m τ₁ τ₂))))
⟨⟩-μ⁻¹-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | no ¬p | yes q =
  ⊥-elim (n≤k⇒¬n≤m+k-contradiction q ¬p)
⟨⟩-μ⁻¹-ren {Γ} {τ₁} {τ₂} -ʳ suc τ | no ¬p | no ¬q with suc τ ∸ τ₂ | inspect (λ (τ , τ₂) → suc τ ∸ τ₂) (τ , τ₂)
... | zero  | [| eq |] =
  ⊥-elim (¬q (m∸n≡0⇒m≤n eq))
... | suc r | [| eq |] with suc r ≤? τ₁
... | yes s rewrite sym eq =
  ⊥-elim (¬p (≤-trans (n≤n∸m+m (suc τ) τ₂) (+-monoˡ-≤ τ₂ s)))
... | no ¬s rewrite sym eq =
  eq-ren (cong (Γ -ᶜ_) (trans (∸-+-assoc (suc τ) τ₂ τ₁) (cong (suc τ ∸_) (+-comm τ₂ τ₁))))

⟨⟩-≤-ren {τ = τ₁} {τ' = τ₂} p -ʳ suc τ with suc τ ≤? τ₁ | suc τ ≤? τ₂
... | yes q | yes r = ⟨⟩-≤-ren (∸-monoˡ-≤ (suc τ) p)
... | yes q | no ¬r = ⊥-elim (¬r (≤-trans q p))
... | no ¬q | yes r =
  wk-⟨⟩-ren ∘ʳ -ᶜ-wk-ren (suc τ ∸ τ₁)
... | no ¬q | no ¬r =
  -ᶜ-≤-ren {τ₁ = suc τ ∸ τ₂} {τ₂ = suc τ ∸ τ₁} (∸-monoʳ-≤ (suc τ) p)

cong-∷-ren ρ  -ʳ suc τ = ρ -ʳ suc τ

cong-⟨⟩-ren {τ = τ'} ρ  -ʳ suc τ with suc τ ≤? τ'
... | yes p = cong-⟨⟩-ren ρ
... | no ¬p = ρ -ʳ (suc τ ∸ τ')

infixl 30 _-ʳ_

-- Action of renamings on variables (showing that reamings
-- allow one to move any variable under more ⟨_⟩ modalities)

var-rename : ∀ {Γ Γ'}
           → Ren Γ Γ'
           →  ∀ {A τ} → A ∈[ τ ] Γ → Σ[ τ' ∈ Time ] (τ ≤ τ' × A ∈[ τ' ] Γ')

var-rename id-ren x =
  _ , ≤-refl , x
  
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
  ≤-reflexive
    (trans
      (cong (_+ τ'') (+-comm τ τ'))
      (+-assoc τ' τ τ'')) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

var-rename (⟨⟩-μ⁻¹-ren {τ = τ} {τ' = τ'}) (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  _ ,
  ≤-reflexive
    (trans
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

-- Interaction of var-split, var-rename, and wk-ctx-ren

var-split₁-wk-ctx-ren : ∀ {Γ Γ' A τ}
                      → (x : A ∈[ τ ] Γ)
                      → proj₁ (var-split x)
                      ≡ proj₁ (var-split
                          (proj₂ (proj₂ (var-rename (wk-ctx-ren {Γ' = Γ'}) x))))

var-split₁-wk-ctx-ren {Γ' = []} x =
  refl
var-split₁-wk-ctx-ren {Γ' = Γ' ∷ A} x =
  var-split₁-wk-ctx-ren {Γ' = Γ'} x
var-split₁-wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} x =
  var-split₁-wk-ctx-ren {Γ' = Γ'} x

var-split₂-wk-ctx-ren : ∀ {Γ Γ' A τ}
                      → (x : A ∈[ τ ] Γ)
                      → proj₁ (proj₂ (var-split x)) ++ᶜ Γ'
                      ≡ proj₁ (proj₂ (var-split
                          (proj₂ (proj₂ (var-rename (wk-ctx-ren {Γ' = Γ'}) x)))))
var-split₂-wk-ctx-ren {Γ' = []} x =
  refl
var-split₂-wk-ctx-ren {Γ' = Γ' ∷ A} x =
  cong (_∷ A) (var-split₂-wk-ctx-ren x)
var-split₂-wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} x =
  cong (_⟨ τ ⟩) (var-split₂-wk-ctx-ren x)

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
  C-rename ρ (unbox {τ = τ} V M) =
    unbox (V-rename (ρ -ʳ τ) V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τs q M)   = delay τs q (C-rename (cong-ren ρ) M)












{-

-- TODO: old stuff, remove at some point

-- Splitting a renaming

split-ren : ∀ {Γ Γ' Γ₁ Γ₂ τ}
          → Ren Γ Γ'
          → Γ₁ , Γ₂ split Γ
          → τ ≤ ctx-time Γ₂
          → Σ[ Γ₁' ∈ Ctx ] Σ[ Γ₂' ∈ Ctx ]
               Ren Γ₁ Γ₁'
             × Γ₁' , Γ₂' split Γ'
             × τ ≤ ctx-time Γ₂'

split-ren {Γ₁ = Γ₁} {Γ₂ = Γ₂} id-ren p q =
  Γ₁ , Γ₂ , id-ren , p , q

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

var-rename id-ren x =
  _ , ≤-refl , x
  
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

-- Interaction of var-split, var-rename, and wk-ctx-ren

var-split₁-wk-ctx-ren : ∀ {Γ Γ' A τ}
                      → (x : A ∈[ τ ] Γ)
                      → proj₁ (var-split x)
                      ≡ proj₁ (var-split
                          (proj₂ (proj₂ (var-rename (wk-ctx-ren {Γ' = Γ'}) x))))

var-split₁-wk-ctx-ren {Γ' = []} x =
  refl
var-split₁-wk-ctx-ren {Γ' = Γ' ∷ A} x =
  var-split₁-wk-ctx-ren {Γ' = Γ'} x
var-split₁-wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} x =
  var-split₁-wk-ctx-ren {Γ' = Γ'} x

var-split₂-wk-ctx-ren : ∀ {Γ Γ' A τ}
                      → (x : A ∈[ τ ] Γ)
                      → proj₁ (proj₂ (var-split x)) ++ᶜ Γ'
                      ≡ proj₁ (proj₂ (var-split
                          (proj₂ (proj₂ (var-rename (wk-ctx-ren {Γ' = Γ'}) x)))))
var-split₂-wk-ctx-ren {Γ' = []} x =
  refl
var-split₂-wk-ctx-ren {Γ' = Γ' ∷ A} x =
  cong (_∷ A) (var-split₂-wk-ctx-ren x)
var-split₂-wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} x =
  cong (_⟨ τ ⟩) (var-split₂-wk-ctx-ren x)

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

-}
