------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------
module Syntax.Renamings where

open import Function hiding (const)

open import Data.Bool hiding (_≤_;_≤?_)
open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Binary.Definitions
open import Relation.Nullary

open import EquationalTheory.CompContext

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Types

open import Data.Nat public
open import Data.Nat.Properties public
open import Util.Equality
open import Util.Time

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)


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
  -- graded monad renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
  ⟨⟩-≤-ren    : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
  -- congruence renamings
  cong-∷-ren  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)

infixr 20 _∘ʳ_

-- some usefull subtitutions for renaming

τ-subst-ren : ∀ {τ τ' Γ} → τ ≡ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ ⟩) → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
τ-subst-ren refl ρ = ρ 

τ-subst-zero : ∀ {τ Γ} → τ ≡ zero → Ren (Γ ⟨ τ ⟩) Γ
τ-subst-zero refl = ⟨⟩-η-ren

τ-subst--ᶜ : ∀ {Γ Γ' τ τ'} → τ ≡ τ' → Ren Γ (Γ' -ᶜ τ) → Ren Γ (Γ' -ᶜ τ')
τ-subst--ᶜ refl ρ = ρ

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

-- Exchange renamings

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = extend-ren (extend-ren wk-ctx-ren Hd) (Tl-∷ Hd)

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren {A = A} {τ = τ} =
     var-ren (Tl-⟨⟩ Hd)
  ∘ʳ cong-ren {Γ'' = [] ⟨ _ ⟩ ∷ _} wk-ren

-- Contraction renaming

contract-ren : ∀ {Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren = var-ren Hd

-- Renaming from an equality of contexts

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren refl = id-ren

-- Renamings preserve time-passage modelled by contexts

ren-≤-ctx-time : ∀ {Γ Γ'}
               → Ren Γ Γ'
               → ctx-time Γ ≤ ctx-time Γ'

ren-≤-ctx-time id-ren =
  ≤-refl
ren-≤-ctx-time (ρ' ∘ʳ ρ) =
  ≤-trans (ren-≤-ctx-time ρ) (ren-≤-ctx-time ρ')
ren-≤-ctx-time wk-ren =
  ≤-refl
ren-≤-ctx-time (var-ren x) =
  ≤-refl
ren-≤-ctx-time ⟨⟩-η-ren =
  ≤-reflexive (+-identityʳ _)
ren-≤-ctx-time ⟨⟩-η⁻¹-ren =
  ≤-reflexive (sym (+-identityʳ _))
ren-≤-ctx-time (⟨⟩-μ-ren {Γ} {τ} {τ'}) =
  ≤-reflexive (sym (+-assoc (ctx-time Γ) τ τ'))
ren-≤-ctx-time (⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'}) =
  ≤-reflexive (+-assoc (ctx-time Γ) τ τ')
ren-≤-ctx-time (⟨⟩-≤-ren {Γ} p) =
  +-monoʳ-≤ (ctx-time Γ) p
ren-≤-ctx-time (cong-∷-ren ρ) =
  ren-≤-ctx-time ρ
ren-≤-ctx-time (cong-⟨⟩-ren {τ = τ} ρ) =
  +-monoˡ-≤ τ (ren-≤-ctx-time ρ)

-- Interactions between the time-travelling operation on contexts and the ⟨_⟩ modality

-ᶜ-⟨⟩-ren : ∀ {Γ} → (τ : Time) → (τ ≤ ctx-time Γ) → Ren ((Γ -ᶜ τ) ⟨ τ ⟩) Γ
-ᶜ-⟨⟩-ren {Γ} zero p =
  ⟨⟩-η-ren
-ᶜ-⟨⟩-ren {Γ ∷ A} (suc τ) p =
     wk-ren 
     ∘ʳ -ᶜ-⟨⟩-ren (suc τ) p
-ᶜ-⟨⟩-ren {Γ ⟨ τ' ⟩} (suc τ) p with suc τ ≤? τ'
... | yes q =
     ⟨⟩-≤-ren (≤-reflexive (m∸n+n≡m q))
  ∘ʳ ⟨⟩-μ⁻¹-ren
... | no ¬q =
     cong-⟨⟩-ren (-ᶜ-⟨⟩-ren {Γ} (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m _ τ'))))
  ∘ʳ ⟨⟩-μ-ren
  ∘ʳ ⟨⟩-≤-ren (≤-reflexive (sym (m∸n+n≡m {suc τ} {τ'} (≰⇒≥ ¬q))))

⟨⟩-ᶜ-ren : ∀ {Γ} → (τ : Time) → Ren (Γ ⟨ τ ⟩ -ᶜ τ) Γ
⟨⟩-ᶜ-ren {Γ} zero = ⟨⟩-η-ren
⟨⟩-ᶜ-ren {Γ} (suc τ) with suc τ ≤? suc τ 
... | yes q = τ-subst-zero (n∸n≡0 τ)
... | no ¬q = ⊥-elim (¬q ≤-refl)

⟨⟩-ᶜ-ren' : ∀ {Γ} → (τ : Time) → Ren Γ (Γ ⟨ τ ⟩ -ᶜ τ)
⟨⟩-ᶜ-ren' {Γ} zero = ⟨⟩-η⁻¹-ren
⟨⟩-ᶜ-ren' {Γ} (suc τ) with suc τ ≤? suc τ 
... | yes q = wk-⟨⟩-ren
... | no ¬q = ⊥-elim (¬q ≤-refl)

-- Weakening renaming for the time-travelling operation on contexts

-ᶜ-wk-ren : ∀ {Γ} → (τ : Time) → Ren (Γ -ᶜ τ) Γ
-ᶜ-wk-ren {Γ} zero =
  id-ren
-ᶜ-wk-ren {[]} (suc τ) =
  id-ren
-ᶜ-wk-ren {Γ ∷ A} (suc τ) =
  wk-ren ∘ʳ -ᶜ-wk-ren {Γ} (suc τ)
-ᶜ-wk-ren {Γ ⟨ τ' ⟩} (suc τ) with suc τ ≤? τ'
... | yes p =
  ⟨⟩-≤-ren (m∸n≤m τ' (suc τ))
... | no ¬p =
  wk-⟨⟩-ren ∘ʳ -ᶜ-wk-ren (suc τ ∸ τ')

-- Monotonicity renaming for the time-travelling operation on contexts

-ᶜ-≤-ren : ∀ {Γ τ₁ τ₂} → τ₁ ≤ τ₂ → Ren (Γ -ᶜ τ₂) (Γ -ᶜ τ₁)
-ᶜ-≤-ren {Γ} {τ₁} {τ₂} p =
     (  (   -ᶜ-wk-ren {Γ -ᶜ τ₁} (τ₂ ∸ τ₁)
         ∘ʳ eq-ren (++ᶜ-ᶜ-+ {Γ} {τ₁} {τ₂ ∸ τ₁}))
     ∘ʳ eq-ren (cong (Γ -ᶜ_) (+-∸-assoc τ₁ {τ₂} {τ₁} p)))
  ∘ʳ eq-ren (cong (Γ -ᶜ_) (sym (m+n∸m≡n τ₁ τ₂)))

-- Time travel and time passage renaming

η-⟨⟩--ᶜ-ren : ∀ {Γ} τ τ' → Ren (Γ -ᶜ τ) (Γ ⟨ τ' ⟩ -ᶜ (τ' + τ))
η-⟨⟩--ᶜ-ren zero τ' = 
    τ-subst--ᶜ (sym (+-identityʳ τ')) (⟨⟩-ᶜ-ren' τ')
η-⟨⟩--ᶜ-ren (suc τ) zero = id-ren
η-⟨⟩--ᶜ-ren (suc τ) (suc τ') with (suc τ' + suc τ) ≤? suc τ' 
... | yes (s≤s q) = ⊥-elim (n+sucm≤n⇒⊥ q)
... | no ¬q = -ᶜ-≤-ren (τ-≤-substₗ (sym (a+b∸a≡b {τ'})) ≤-refl) 

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
... | zero  | [| eq |] =
  ⊥-elim (¬q (m∸n≡0⇒m≤n eq))
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

-- Lemma that allows to substract and add the same time

+-∸-id-ren : ∀ {Γ} τ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ ∸ τ' + τ' ⟩)
+-∸-id-ren τ zero = ⟨⟩-≤-ren (≤-stepsʳ zero ≤-refl)
+-∸-id-ren τ (suc τ') = ⟨⟩-≤-ren (τ-≤-substᵣ (+-comm (τ ∸ suc τ') (suc τ')) (m≤n+m∸n τ (suc τ')))

-- Another time travel and time passage relation

wk-⟨⟩--ᶜ-ren : ∀ {Γ τ τ'} → τ ≤ τ' → τ' ≤ ctx-time Γ → Ren ((Γ -ᶜ τ') ⟨ τ ⟩) Γ
wk-⟨⟩--ᶜ-ren {_} {zero} {τ'} p q = -ᶜ-wk-ren τ' ∘ʳ ⟨⟩-η-ren
wk-⟨⟩--ᶜ-ren {Γ ∷ x} {suc τ} {suc τ'} p q = wk-ren ∘ʳ wk-⟨⟩--ᶜ-ren p q
wk-⟨⟩--ᶜ-ren {Γ ⟨ τ'' ⟩} {suc τ} {suc τ'} p q with suc τ' ≤? τ'' 
... | yes r = ⟨⟩-≤-ren (τ''∸τ'+τ≤τ'' τ'' (suc τ') (suc τ) p r) ∘ʳ ⟨⟩-μ⁻¹-ren
wk-⟨⟩--ᶜ-ren {Γ ⟨ τ'' ⟩} {suc τ} {suc τ'} p q | no ¬r = 
     (cong-⟨⟩-ren (wk-⟨⟩--ᶜ-ren {τ' = suc τ' ∸ τ'' } 
                    (∸-monoˡ-≤ τ'' p) 
                    (m≤n+k⇒m∸k≤n (suc τ') (ctx-time Γ) τ'' q)) 
      ∘ʳ ⟨⟩-μ-ren {Γ = Γ -ᶜ (suc τ' ∸ τ'')} {τ = suc τ ∸ τ''} {τ' = τ''}) 
        ∘ʳ +-∸-id-ren (suc τ) τ''


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

  V-rename ρ (var x)    = var (proj₂ (proj₂ (var-rename ρ x)))
  V-rename ρ (const c)  = const c
  V-rename ρ ⋆          = ⋆
  V-rename ρ (⦉ V , W ⦊) = ⦉ V-rename ρ V , V-rename ρ W ⦊
  V-rename ρ (lam M)    = lam (C-rename (cong-ren ρ) M)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename ρ (return V)       = return (V-rename ρ V)
  C-rename ρ (M ; N)          = C-rename ρ M ; C-rename (cong-ren ρ) N
  C-rename ρ (V · W)          = V-rename ρ V · V-rename ρ W
  C-rename ρ (match V `in M)  = match V-rename ρ V `in C-rename (cong-ren ρ) M
  C-rename ρ (absurd V)       = absurd (V-rename ρ V)
  C-rename ρ (perform op V M) = perform op (V-rename ρ V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τ M)      = delay τ (C-rename (cong-ren ρ) M)
  C-rename ρ (handle M `with H `in N) =
    handle C-rename ρ M
    `with (λ op τ'' → C-rename (cong-ren ρ) (H op τ'') )
    `in (C-rename (cong-ren ρ) N)
  C-rename ρ (unbox {τ = τ} p V M) =
    unbox (≤-trans p (ren-≤-ctx-time ρ)) (V-rename (ρ -ʳ τ) V) (C-rename (cong-ren ρ) M)
  C-rename ρ (box V M)         = box (V-rename (cong-ren ρ) V) (C-rename (cong-ren ρ) M)

-----------------------------------
-- Renamings of binding contexts --
-----------------------------------

-- lemma that states that joining contexts is context sumation under the hood

Γ⋈Δ≡Γ++ᶜctxΔ : (Γ : Ctx) → (Δ : BCtx) → Γ ⋈ Δ ≡ Γ ++ᶜ (BCtx→Ctx Δ)
Γ⋈Δ≡Γ++ᶜctxΔ Γ []ₗ = refl
Γ⋈Δ≡Γ++ᶜctxΔ Γ (X ∷ₗ Δ) = 
  begin 
      Γ ⋈ (X ∷ₗ Δ) ≡⟨ refl ⟩  
      (Γ ∷ X) ⋈ Δ ≡⟨ Γ⋈Δ≡Γ++ᶜctxΔ (Γ ∷ X) Δ ⟩ 
      (Γ ∷ X) ++ᶜ (BCtx→Ctx Δ) ≡⟨ (++ᶜ-assoc Γ ([] ∷ X) (BCtx→Ctx Δ)) ⟩
      Γ ++ᶜ (([] ∷ X) ++ᶜ (BCtx→Ctx Δ))
    ∎
Γ⋈Δ≡Γ++ᶜctxΔ Γ (⟨ τ ⟩ₗ Δ) = 
    begin 
      Γ ⋈ (⟨ τ ⟩ₗ Δ) ≡⟨ refl ⟩  
      (Γ ⟨ τ ⟩) ⋈ Δ ≡⟨ Γ⋈Δ≡Γ++ᶜctxΔ (Γ ⟨ τ ⟩) Δ ⟩ 
      (Γ ⟨ τ ⟩) ++ᶜ (BCtx→Ctx Δ) ≡⟨ (++ᶜ-assoc Γ ([] ⟨ τ ⟩) (BCtx→Ctx Δ)) ⟩
      Γ ++ᶜ (([] ⟨ τ ⟩) ++ᶜ (BCtx→Ctx Δ))
    ∎

-- substitute context under the ctx-time

subst-ctx-time : ∀ {Γ Δ} → Γ ≡ Δ → ctx-time Γ ≡ ctx-time Δ
subst-ctx-time refl = refl

-- time on ⋈ is homogenous

time[Γ⋈Δ]≡time[Γ]+time[Δ] : (Γ : Ctx) → (Δ : BCtx) → ctx-time (Γ ⋈ Δ) ≡ ctx-time Γ + (ctx-time (BCtx→Ctx Δ))
time[Γ⋈Δ]≡time[Γ]+time[Δ] Γ Δ = 
  begin 
      ctx-time (Γ ⋈ Δ) ≡⟨ subst-ctx-time (Γ⋈Δ≡Γ++ᶜctxΔ Γ Δ) ⟩  
      ctx-time (Γ ++ᶜ (BCtx→Ctx Δ)) ≡⟨ ctx-time-++ᶜ Γ ((BCtx→Ctx Δ)) ⟩  
      ctx-time Γ + ctx-time (BCtx→Ctx Δ)
    ∎

-- Lemma: ⋈ with binding context increase time on left

τΓ≤τΓ⋈Δ : ∀ {Γ Δ τ} → τ ≤ ctx-time Γ → τ ≤ ctx-time (Γ ⋈ Δ)
τΓ≤τΓ⋈Δ {Γ} {Δ} p = τ-≤-substᵣ (time[Γ⋈Δ]≡time[Γ]+time[Δ] Γ Δ) (≤-stepsʳ (ctx-time (BCtx→Ctx Δ)) p)

-- Lemma: ⋈  with binding context increase time on right

τΔ≤τΓ⋈Δ : ∀ {Γ Δ τ} → τ ≤ ctx-time (BCtx→Ctx Δ) → τ ≤ ctx-time (Γ ⋈ Δ)
τΔ≤τΓ⋈Δ {Γ} {Δ} p = τ-≤-substᵣ (time[Γ⋈Δ]≡time[Γ]+time[Δ] Γ Δ) (≤-stepsˡ (ctx-time Γ) p)

-- weakening lemma

renΓΓ⟨τ'⟩-τ : ∀ {Γ τ τ'} → τ ≤ τ' → Ren Γ (Γ ⟨ τ' ⟩ -ᶜ τ)
renΓΓ⟨τ'⟩-τ {Γ} {τ} {τ'} p = ⟨⟩-≤-ren p -ʳ τ ∘ʳ ⟨⟩-ᶜ-ren' τ

-- weakening lemma 

-ᶜ-++ᶜ-wk-ren : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → Ren Γ (Γ ++ᶜ Γ' -ᶜ τ)
-ᶜ-++ᶜ-wk-ren {Γ} {Γ'} {τ} p = (eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ∘ʳ wk-ctx-ren

-- -ᶜ for joined contexts lemmas

Γ⋈Δ-ᶜτ : ∀ {Γ Δ τ} → τ ≤ ctx-time (BCtx→Ctx Δ) → Ren Γ (Γ ⋈ Δ -ᶜ τ)
Γ⋈Δ-ᶜτ {Γ} {Δ} {τ} p = eq-ren (sym (Γ⋈Δ≡Γ++ᶜctxΔ Γ Δ)) -ʳ τ ∘ʳ -ᶜ-++ᶜ-wk-ren p

-- rename time to context

ren⟨τ⟩-ctx : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → Ren (Γ ⟨ τ ⟩) (Γ ++ᶜ Γ')
ren⟨τ⟩-ctx {Γ} {[]} {.zero} z≤n = ⟨⟩-η-ren
ren⟨τ⟩-ctx {Γ} {Γ' ∷ X} {τ} p = wk-ren ∘ʳ ren⟨τ⟩-ctx p
ren⟨τ⟩-ctx {Γ} {Γ' ⟨ τ' ⟩} {τ} p with τ ≤? τ'
... | yes q = cong-⟨⟩-ren wk-ctx-ren ∘ʳ (⟨⟩-≤-ren q) 
... | no ¬q = 
        (cong-⟨⟩-ren (ren⟨τ⟩-ctx (m≤n+k⇒m∸k≤n τ (ctx-time Γ') τ' p)) 
            ∘ʳ ⟨⟩-μ-ren {τ = τ ∸ τ'}) 
        ∘ʳ +-∸-id-ren τ τ'

-- elim nonused variables from the joined contex 

renΓ⟨τ⟩-Γ⋈Δ : ∀ {Γ Δ A τ} → τ ≤ ctx-time (BCtx→Ctx Δ) → Ren (Γ ⟨ τ ⟩) (Γ ∷ A ⋈ Δ)
renΓ⟨τ⟩-Γ⋈Δ {Γ} {Δ} {A} {τ} p = 
    ((eq-ren (sym (Γ⋈Δ≡Γ++ᶜctxΔ (Γ ∷ A) Δ))) 
    ∘ʳ cong-ren wk-ren) 
    ∘ʳ ren⟨τ⟩-ctx p 