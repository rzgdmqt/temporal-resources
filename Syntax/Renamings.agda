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

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings.Raw public
open import Syntax.Types

open import Data.Nat public
open import Data.Nat.Properties public
open import Util.Equality
open import Util.Time

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

-- Variable renamings (with an extra condition that disallow discarding time captured by contexts)

record Ren (Γ Γ' : Ctx) : Set where
  constructor ren
  field
    ctx-time-≤ : ctx-time Γ ≤ ctx-time Γ'
    var-rename : VRen Γ Γ'

open Ren public

-- Lifting the operations on VRen to Ren

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {Γ} =
  ren ≤-refl id-vren

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
ρ' ∘ʳ ρ =
  ren
    (≤-trans (ctx-time-≤ ρ) (ctx-time-≤ ρ'))
    ((var-rename ρ') ∘ᵛʳ (var-rename ρ))

infixr 20 _∘ʳ_

-- Equality renaming

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren p =
  ren
    (≤-reflexive (cong ctx-time p))
    (eq-vren p)

-- Variable weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ A)
wk-ren {Γ} {A} =
  ren ≤-refl (wk-vren {Γ} {A})

-- Time weakening renaming

wk-⟨⟩-ren : ∀ {Γ τ} → Ren Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-ren {Γ} {τ} =
  ren (m≤m+n (ctx-time Γ) τ) (wk-⟨⟩-vren {Γ} {τ})

-- Strong monoidal structure of ⟨_⟩

⟨⟩-η-ren : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
⟨⟩-η-ren {Γ} = 
  ren 
    (τ-≤-substₗ (sym (+-identityʳ (ctx-time Γ))) ≤-refl) 
    ⟨⟩-η-vren

⟨⟩-η⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
⟨⟩-η⁻¹-ren = wk-⟨⟩-ren

⟨⟩-μ-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-μ-ren {Γ} {τ} {τ'} = 
  ren 
    (τ-≤-substₗ (+-assoc (ctx-time Γ) τ τ') ≤-refl) 
    ⟨⟩-μ-vren

⟨⟩-μ⁻¹-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} = 
  ren 
    (τ-≤-substₗ (sym (+-assoc (ctx-time Γ) τ τ')) ≤-refl)
    ⟨⟩-μ⁻¹-vren

-- Variable congruence renaming

cong-∷-ren : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
cong-∷-ren ρ =
  ren (ctx-time-≤ ρ) (cong-∷-vren (var-rename ρ))

-- Time congruence renaming

cong-⟨⟩-ren : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)
cong-⟨⟩-ren {τ = τ} ρ =
  ren (+-monoˡ-≤ τ (ctx-time-≤ ρ)) (cong-⟨⟩-vren (var-rename ρ))

-- General congruence renaming

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ} {Γ'} {Γ''} ρ =
  ren
    (≤-trans
      (≤-reflexive (ctx-time-++ᶜ Γ Γ''))
      (≤-trans
        (+-monoˡ-≤ (ctx-time Γ'') (ctx-time-≤ ρ))
        (≤-reflexive (sym (ctx-time-++ᶜ Γ' Γ'')))))
    (cong-vren (var-rename ρ))

-- General weakening renamings

wk-ctx-renᵣ : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-renᵣ {Γ} {Γ'} = 
  ren 
    (τ-≤-substᵣ (ctx-time-++ᶜ Γ Γ') (≤-stepsʳ (ctx-time Γ') ≤-refl)) 
    wk-ctx-vren

wk-ctx-renₗ : ∀ {Γ Γ'} → Ren Γ (Γ' ++ᶜ Γ)
wk-ctx-renₗ {Γ} {Γ'} = 
  cong-ren {Γ' = Γ'} (eq-ren ++ᶜ-identityˡ ∘ʳ wk-ctx-renᵣ) 
    ∘ʳ (eq-ren (sym ++ᶜ-identityˡ))

-- Monotonicity renaming for ⟨_⟩

⟨⟩-≤-ren : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
⟨⟩-≤-ren {Γ} p = 
  ren 
    (+-monoʳ-≤ (ctx-time Γ) p) 
    (⟨⟩-≤-vren p)

-- Time and variable exchange renaming

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren = 
  ren 
    ≤-refl 
    exch-⟨⟩-var-vren

-- Variable exchange renaming

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = 
  ren 
    ≤-refl 
    exch-vren

-- Time travelling operation on contexts

_-ʳ_,_ : ∀ {Γ Γ'} → Ren Γ Γ' → (τ : Time) → τ ≤ ctx-time Γ → Ren (Γ -ᶜ τ) (Γ' -ᶜ τ)
_-ʳ_,_ {Γ} {Γ'} ρ τ p =
  ren
    (≤-trans
      (≤-reflexive (ctx-time-ᶜ-∸ Γ τ p))
      (≤-trans
        (∸-monoˡ-≤ τ (ctx-time-≤ ρ))
        (≤-reflexive (sym (ctx-time-ᶜ-∸ Γ' τ (≤-trans p (ctx-time-≤ ρ)))))))
    ((var-rename ρ) -ᵛʳ τ)

-- Weakening a time to a context renaming

ren⟨τ⟩-ctx : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → Ren (Γ ⟨ τ ⟩) (Γ ++ᶜ Γ')
ren⟨τ⟩-ctx {Γ} {Γ'} {τ} p =
  ren
    (≤-trans
      (+-monoʳ-≤ (ctx-time Γ) p)
      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))
    (vren⟨τ⟩-ctx p)

infixl 30 _-ʳ_,_

-- Reflexivity equality renamings' interaction with identity renamings

eq-ren-refl-id : ∀ {Γ}
               → eq-ren refl ≡ id-ren {Γ}
                
eq-ren-refl-id {Γ} =
  cong₂ ren refl refl

-- Congruence renamings' interaction with identities (functoriality)

cong-ren-id : ∀ {Γ Γ'}
            → cong-ren {Γ'' = Γ'} (id-ren {Γ}) ≡ id-ren

cong-ren-id {Γ} {Γ'} =
  cong₂ ren
    (≤-irrelevant _ _)
    (ifun-ext (λ {A} → ifun-ext (λ {τ} → fun-ext (λ x →
      cong-vren-id {Γ} {Γ'} x))))

-- Congruence renamings' interaction with composition (functoriality)

cong-ren-fun : ∀ {Γ Γ' Γ'' Γ'''}
             → (ρ : Ren Γ Γ')
             → (ρ' : Ren Γ' Γ'')
             → cong-ren {Γ'' = Γ'''} (ρ' ∘ʳ ρ)
             ≡ cong-ren ρ' ∘ʳ cong-ren ρ

cong-ren-fun {Γ} {Γ'} {Γ''} {Γ'''} ρ ρ' =
  cong₂ ren
    (≤-irrelevant _ _)
    (ifun-ext (λ {A} → ifun-ext (λ {τ} → fun-ext (λ x → cong-vren-fun (var-rename ρ) (var-rename ρ') x))))

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
    unbox (≤-trans p (ctx-time-≤ ρ)) (V-rename (ρ -ʳ τ , p) V) (C-rename (cong-ren ρ) M)
  C-rename ρ (box V M)        = box (V-rename (cong-ren ρ) V) (C-rename (cong-ren ρ) M)

-- Identity law of the action of renamings
{-
mutual

  V-rename-id : ∀ {Γ A}
              → (V : Γ ⊢V⦂ A)
              → V-rename id-ren V
              ≡ V

  V-rename-id (var x) =
    refl
  V-rename-id (const c) =
    refl
  V-rename-id ⋆ =
    refl
  V-rename-id ⦉ V , W ⦊ =
    cong₂ ⦉_,_⦊ (V-rename-id V) (V-rename-id W)
  V-rename-id {Γ} (lam M) =
    cong lam
      (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-id {Γ}))
        (C-rename-id M))

  C-rename-id : ∀ {Γ C}
              → (M : Γ ⊢C⦂ C)
              → C-rename id-ren M
              ≡ M

  C-rename-id (return V) =
    cong return (V-rename-id V)
  C-rename-id {Γ} (M ; N) =
    cong₂ _;_
      (C-rename-id M)
      (trans
        (cong (λ ρ → C-rename ρ N) (cong-ren-id {Γ}))
        (C-rename-id N))
  C-rename-id {Γ} (V · W) =
    cong₂ _·_ (V-rename-id V) (V-rename-id W)
  C-rename-id {Γ} (match V `in M) =
    cong₂ match_`in_
      (V-rename-id V)
      (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-id {Γ}))
        (C-rename-id M))
  C-rename-id {Γ} (absurd V) =
    cong absurd (V-rename-id V)
  C-rename-id {Γ} (perform op V M) =
    cong₂ (perform op)
      (V-rename-id V)
      (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-id {Γ}))
        (C-rename-id M))
  C-rename-id {Γ} (delay τ M) =
    cong (delay τ)
    (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-id {Γ}))
        (C-rename-id M))
  C-rename-id {Γ} (handle M `with H `in N) =
    cong₃ (handle_`with_`in)
      (C-rename-id M)
      (fun-ext (λ op → fun-ext (λ τ'' →
        trans
          (cong (λ ρ → C-rename ρ (H op τ'')) (cong-ren-id {Γ}))
          (C-rename-id (H op τ'')))))
      (trans
        (cong (λ ρ → C-rename ρ N) (cong-ren-id {Γ}))
        (C-rename-id N))
  C-rename-id {Γ} (unbox p V M) =
    cong₃ unbox
      (≤-irrelevant _ _)
      {!!}
      (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-id {Γ}))
        (C-rename-id M))
  C-rename-id {Γ} (box V M) =
    cong₂ box
      (trans
        (cong (λ ρ → V-rename ρ V) (cong-ren-id {Γ}))
        (V-rename-id V))
      (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-id {Γ}))
        (C-rename-id M))
-}

-- Transitivity law of the action of renamings

-- TODO: temporarily commented out

{-
mutual

  V-rename-trans : ∀ {Γ Γ' Γ'' A}
                 → (ρ : Ren Γ Γ')
                 → (ρ' : Ren Γ' Γ'')
                 → (V : Γ ⊢V⦂ A)
                 → V-rename (ρ' ∘ʳ ρ) V
                 ≡ V-rename ρ' (V-rename ρ V)

  V-rename-trans ρ ρ' (var x) =
    refl
  V-rename-trans ρ ρ' (const c) =
    refl 
  V-rename-trans ρ ρ' ⋆ =
    refl
  V-rename-trans ρ ρ' ⦉ V , W ⦊ =
    cong₂ ⦉_,_⦊
      (V-rename-trans ρ ρ' V)
      (V-rename-trans ρ ρ' W)
  V-rename-trans ρ ρ' (lam M) =
    cong lam
      (trans
        (cong (λ ρ → C-rename ρ M) (cong-ren-fun ρ ρ'))
        (C-rename-trans (cong-ren ρ) (cong-ren ρ') M))

  C-rename-trans : ∀ {Γ Γ' Γ'' C}
                 → (ρ : Ren Γ Γ')
                 → (ρ' : Ren Γ' Γ'')
                 → (M : Γ ⊢C⦂ C)
                 → C-rename (ρ' ∘ʳ ρ) M
                 ≡ C-rename ρ' (C-rename ρ M)

  C-rename-trans ρ ρ' (return V) =
    cong return
      (V-rename-trans ρ ρ' V)
  C-rename-trans ρ ρ' (M ; N) =
    cong₂ _;_
      (C-rename-trans ρ ρ' M)
      (trans
         (cong (λ ρ → C-rename ρ N) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') N))
  C-rename-trans ρ ρ' (V · W) =
    cong₂ _·_
      (V-rename-trans ρ ρ' V)
      (V-rename-trans ρ ρ' W)
  C-rename-trans ρ ρ' (match V `in N) =
    cong₂ (match_`in_)
      (V-rename-trans ρ ρ' V)
      (trans
         (cong (λ ρ → C-rename ρ N) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') N))
  C-rename-trans ρ ρ' (absurd V) =
    cong absurd
      (V-rename-trans ρ ρ' V)
  C-rename-trans ρ ρ' (perform op V M) =
    cong₂ (perform op)
      (V-rename-trans ρ ρ' V)
      (trans
         (cong (λ ρ → C-rename ρ M) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') M))
  C-rename-trans ρ ρ' (delay τ M) =
    cong (delay τ)
      (trans
         (cong (λ ρ → C-rename ρ M) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') M))
  C-rename-trans ρ ρ' (handle M `with H `in N) =
    cong₃ (handle_`with_`in)
      (C-rename-trans ρ ρ' M)
      (fun-ext (λ op → fun-ext (λ τ'' →
        trans
          (cong (λ ρ → C-rename ρ (H op τ'')) (cong-ren-fun ρ ρ'))
          (C-rename-trans (cong-ren ρ) (cong-ren ρ') (H op τ'')))))
      (trans
         (cong (λ ρ → C-rename ρ N) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') N))
  C-rename-trans ρ ρ' (unbox {τ = τ} p V M) =
    cong₃ unbox
      (≤-irrelevant _ _)
      (trans
        (cong (λ ρ → V-rename ρ V) {!!}) -- TODO: need lemmas relating renaming with ∘ʳ and -ʳ
        (V-rename-trans _ _ V))
      (trans
         (cong (λ ρ → C-rename ρ M) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') M))
  C-rename-trans ρ ρ' (box V M) =
    cong₂ box
      (trans
         (cong (λ ρ → V-rename ρ V) (cong-ren-fun ρ ρ'))
         (V-rename-trans (cong-ren ρ) (cong-ren ρ') V))
      (trans
         (cong (λ ρ → C-rename ρ M) (cong-ren-fun ρ ρ'))
         (C-rename-trans (cong-ren ρ) (cong-ren ρ') M))
-}










{- ------------------------------------------------------- -}
{- ------------------------------------------------------- -}
{- ------------------------------------------------------- -}


{-

-- Variable renamings (as the least relation closed under
-- identities, composition, ordinary variable renamings,
-- and graded monad operations for the ⟨_⟩ modality).

data VRen : Ctx → Ctx → Set where
  -- identity renaming
  id-ren      : ∀ {Γ} → VRen Γ Γ
  -- composition of renamings
  _∘ʳ_        : ∀ {Γ Γ' Γ''} → VRen Γ' Γ'' → VRen Γ Γ' → VRen Γ Γ''
  -- weakening renaming
  wk-ren      : ∀ {Γ A} → VRen Γ (Γ ∷ A)
  -- variable renaming
  var-ren     : ∀ {Γ A τ} → A ∈[ τ ] Γ → VRen (Γ ∷ A) Γ
  -- graded monad renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → VRen (Γ ⟨ 0 ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → VRen Γ (Γ ⟨ 0 ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ τ τ'} → VRen (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ τ τ'} → VRen (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
  ⟨⟩-≤-ren    : ∀ {Γ τ τ'} → τ ≤ τ' → VRen (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
  -- congruence renamings
  cong-∷-ren  : ∀ {Γ Γ' A} → VRen Γ Γ' → VRen (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' τ} → VRen Γ Γ' → VRen (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)

infixr 20 _∘ʳ_

-- some usefull subtitutions for renaming

τ-subst-ren : ∀ {τ τ' Γ} → τ ≡ τ' → VRen (Γ ⟨ τ ⟩) (Γ ⟨ τ ⟩) → VRen (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
τ-subst-ren refl ρ = ρ 

τ-subst-zero : ∀ {τ Γ} → τ ≡ zero → VRen (Γ ⟨ τ ⟩) Γ
τ-subst-zero refl = ⟨⟩-η-ren

τ-subst--ᶜ : ∀ {Γ Γ' τ τ'} → τ ≡ τ' → VRen Γ (Γ' -ᶜ τ) → VRen Γ (Γ' -ᶜ τ')
τ-subst--ᶜ refl ρ = ρ

-- Extending a renaming with a variable

extend-ren : ∀ {Γ Γ' A τ} → VRen Γ Γ' → A ∈[ τ ] Γ' → VRen (Γ ∷ A) Γ'
extend-ren ρ x = var-ren x ∘ʳ cong-∷-ren ρ

-- Congruence of renamings

cong-ren : ∀ {Γ Γ' Γ''} → VRen Γ Γ' → VRen (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []} ρ        = ρ
cong-ren {Γ'' = Γ'' ∷ A} ρ   = cong-∷-ren (cong-ren ρ)
cong-ren {Γ'' = Γ'' ⟨ τ ⟩} ρ = cong-⟨⟩-ren (cong-ren ρ)

-- Weakening by a modality renaming

wk-⟨⟩-ren : ∀ {Γ τ} → VRen Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-ren = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren

-- Weakening by a context renaming

wk-ctx-renᵣ : ∀ {Γ Γ'} → VRen Γ (Γ ++ᶜ Γ')
wk-ctx-renᵣ {Γ' = []}       = id-ren
wk-ctx-renᵣ {Γ' = Γ' ∷ A}   = wk-ren ∘ʳ wk-ctx-renᵣ
wk-ctx-renᵣ {Γ' = Γ' ⟨ τ ⟩} = wk-⟨⟩-ren ∘ʳ wk-ctx-renᵣ

-- Exchange renamings

exch-ren : ∀ {Γ A B} → VRen (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = extend-ren (extend-ren wk-ctx-renᵣ Hd) (Tl-∷ Hd)

exch-⟨⟩-var-ren : ∀ {Γ A τ} → VRen (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren {A = A} {τ = τ} =
     var-ren (Tl-⟨⟩ Hd)
  ∘ʳ cong-ren {Γ'' = [] ⟨ _ ⟩ ∷ _} wk-ren

-- Contraction renaming

contract-ren : ∀ {Γ A} → VRen (Γ ∷ A ∷ A) (Γ ∷ A)
contract-ren = var-ren Hd

-- VRenaming from an equality of contexts

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → VRen Γ Γ'
eq-ren refl = id-ren

-- VRenaming from an empty context 

empty-ren : ∀ {Γ} → VRen [] Γ 
empty-ren {[]} = id-ren
empty-ren {Γ ∷ A} = wk-ren ∘ʳ empty-ren
empty-ren {Γ ⟨ τ ⟩} = wk-⟨⟩-ren ∘ʳ empty-ren

-- VRenamings preserve time-passage modelled by contexts

ren-≤-ctx-time : ∀ {Γ Γ'}
               → VRen Γ Γ'
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

-ᶜ-⟨⟩-ren : ∀ {Γ} → (τ : Time) → (τ ≤ ctx-time Γ) → VRen ((Γ -ᶜ τ) ⟨ τ ⟩) Γ
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

⟨⟩-ᶜ-ren : ∀ {Γ} → (τ : Time) → VRen (Γ ⟨ τ ⟩ -ᶜ τ) Γ
⟨⟩-ᶜ-ren {Γ} zero = ⟨⟩-η-ren
⟨⟩-ᶜ-ren {Γ} (suc τ) with suc τ ≤? suc τ 
... | yes q = τ-subst-zero (n∸n≡0 τ)
... | no ¬q = ⊥-elim (¬q ≤-refl)

⟨⟩-ᶜ-ren' : ∀ {Γ} → (τ : Time) → VRen Γ (Γ ⟨ τ ⟩ -ᶜ τ)
⟨⟩-ᶜ-ren' {Γ} zero = ⟨⟩-η⁻¹-ren
⟨⟩-ᶜ-ren' {Γ} (suc τ) with suc τ ≤? suc τ 
... | yes q = wk-⟨⟩-ren
... | no ¬q = ⊥-elim (¬q ≤-refl)

-- Weakening renaming for the time-travelling operation on contexts

-ᶜ-wk-ren : ∀ {Γ} → (τ : Time) → VRen (Γ -ᶜ τ) Γ
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

-ᶜ-≤-ren : ∀ {Γ τ₁ τ₂} → τ₁ ≤ τ₂ → VRen (Γ -ᶜ τ₂) (Γ -ᶜ τ₁)
-ᶜ-≤-ren {Γ} {τ₁} {τ₂} p =
     (  (   -ᶜ-wk-ren {Γ -ᶜ τ₁} (τ₂ ∸ τ₁)
         ∘ʳ eq-ren (++ᶜ-ᶜ-+ {Γ} {τ₁} {τ₂ ∸ τ₁}))
     ∘ʳ eq-ren (cong (Γ -ᶜ_) (+-∸-assoc τ₁ {τ₂} {τ₁} p)))
  ∘ʳ eq-ren (cong (Γ -ᶜ_) (sym (m+n∸m≡n τ₁ τ₂)))

-- Time travel and time passage renaming

η-⟨⟩--ᶜ-ren : ∀ {Γ} τ τ' → VRen (Γ -ᶜ τ) (Γ ⟨ τ' ⟩ -ᶜ (τ' + τ))
η-⟨⟩--ᶜ-ren zero τ' = 
    τ-subst--ᶜ (sym (+-identityʳ τ')) (⟨⟩-ᶜ-ren' τ')
η-⟨⟩--ᶜ-ren (suc τ) zero = id-ren
η-⟨⟩--ᶜ-ren (suc τ) (suc τ') with (suc τ' + suc τ) ≤? suc τ' 
... | yes (s≤s q) = ⊥-elim (n+sucm≤n⇒⊥ q)
... | no ¬q = -ᶜ-≤-ren (τ-≤-substₗ (sym (a+b∸a≡b {τ'})) ≤-refl) 

-- Time-travelling operation on renamings

_-ʳ_ : ∀ {Γ Γ'} → VRen Γ Γ' → (τ : Time) → VRen (Γ -ᶜ τ) (Γ' -ᶜ τ)
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

+-∸-id-ren : ∀ {Γ} τ τ' → VRen (Γ ⟨ τ ⟩) (Γ ⟨ τ ∸ τ' + τ' ⟩)
+-∸-id-ren τ zero = ⟨⟩-≤-ren (≤-stepsʳ zero ≤-refl)
+-∸-id-ren τ (suc τ') = ⟨⟩-≤-ren (τ-≤-substᵣ (+-comm (τ ∸ suc τ') (suc τ')) (m≤n+m∸n τ (suc τ')))

-- Another time travel and time passage relation

wk-⟨⟩--ᶜ-ren : ∀ {Γ τ τ'} → τ ≤ τ' → τ' ≤ ctx-time Γ → VRen ((Γ -ᶜ τ') ⟨ τ ⟩) Γ
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
           → VRen Γ Γ'
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

-- Interaction of var-split, var-rename, and wk-ctx-renᵣ

var-split₁-wk-ctx-ren : ∀ {Γ Γ' A τ}
                      → (x : A ∈[ τ ] Γ)
                      → proj₁ (var-split x)
                      ≡ proj₁ (var-split
                          (proj₂ (proj₂ (var-rename (wk-ctx-renᵣ {Γ' = Γ'}) x))))

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
                          (proj₂ (proj₂ (var-rename (wk-ctx-renᵣ {Γ' = Γ'}) x)))))
var-split₂-wk-ctx-ren {Γ' = []} x =
  refl
var-split₂-wk-ctx-ren {Γ' = Γ' ∷ A} x =
  cong (_∷ A) (var-split₂-wk-ctx-ren x)
var-split₂-wk-ctx-ren {Γ' = Γ' ⟨ τ ⟩} x =
  cong (_⟨ τ ⟩) (var-split₂-wk-ctx-ren x)

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → VRen Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename ρ (var x)    = var (proj₂ (proj₂ (var-rename ρ x)))
  V-rename ρ (const c)  = const c
  V-rename ρ ⋆          = ⋆
  V-rename ρ (⦉ V , W ⦊) = ⦉ V-rename ρ V , V-rename ρ W ⦊
  V-rename ρ (lam M)    = lam (C-rename (cong-ren ρ) M)

  C-rename : ∀ {Γ Γ' C}
           → VRen Γ Γ'
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


{-
-- Transitivity of the actions of renaming

mutual

  V-rename-trans : ∀ {Γ Γ' Γ'' Γ''' A}
                 → (ρ : VRen Γ Γ')
                 → (ρ' : VRen Γ' Γ'')
                 → (V : Γ ++ᶜ Γ''' ⊢V⦂ A)
                 → V-rename (cong-ren (ρ' ∘ʳ ρ)) V
                 ≡ V-rename (cong-ren ρ') (V-rename (cong-ren ρ) V)

  V-rename-trans ρ ρ' (var x) =
    {!!} -- need lemma relating var-rename with ∘ʳ
  V-rename-trans ρ ρ' (const c) =
    refl 
  V-rename-trans ρ ρ' ⋆ =
    refl
  V-rename-trans ρ ρ' ⦉ V , W ⦊ =
    cong₂ ⦉_,_⦊
      (V-rename-trans ρ ρ' V)
      (V-rename-trans ρ ρ' W)
  V-rename-trans ρ ρ' (lam M) =
    cong lam (C-rename-trans ρ ρ' M)

  C-rename-trans : ∀ {Γ Γ' Γ'' Γ''' C}
                 → (ρ : VRen Γ Γ')
                 → (ρ' : VRen Γ' Γ'')
                 → (M : Γ ++ᶜ Γ''' ⊢C⦂ C)
                 → C-rename (cong-ren (ρ' ∘ʳ ρ)) M
                 ≡ C-rename (cong-ren ρ') (C-rename (cong-ren ρ) M)

  C-rename-trans ρ ρ' (return V) =
    cong return
      (V-rename-trans ρ ρ' V)
  C-rename-trans ρ ρ' (M ; N) =
    cong₂ _;_
      (C-rename-trans ρ ρ' M)
      (C-rename-trans _ _ N)
  C-rename-trans ρ ρ' (V · W) =
    cong₂ _·_
      (V-rename-trans ρ ρ' V)
      (V-rename-trans ρ ρ' W)
  C-rename-trans ρ ρ' (match V `in N) =
    cong₂ (match_`in_)
      (V-rename-trans ρ ρ' V)
      (C-rename-trans _ _ N)
  C-rename-trans ρ ρ' (absurd V) =
    cong absurd
      (V-rename-trans ρ ρ' V)
  C-rename-trans ρ ρ' (perform op V M) =
    cong₂ (perform op)
      (V-rename-trans ρ ρ' V)
      (C-rename-trans _ _ M)
  C-rename-trans ρ ρ' (delay τ M) =
    cong (delay τ)
      (C-rename-trans _ _ M)
  C-rename-trans ρ ρ' (handle M `with H `in N) =
    cong₃ (handle_`with_`in)
      (C-rename-trans ρ ρ' M)
      (fun-ext (λ op → fun-ext (λ τ'' →
        C-rename-trans _ _ (H op τ''))))
      (C-rename-trans _ _ N)
  C-rename-trans ρ ρ' (unbox {τ = τ} p V M) =
    cong₃ unbox
      (≤-irrelevant _ _)
      {!!} -- TODO: need lemma relating renaming with ∘ʳ and -ʳ
      (C-rename-trans _ _ M)
  C-rename-trans ρ ρ' (box V M) =
    cong₂ box
      (V-rename-trans _ _ V)
      (C-rename-trans _ _ M)
-}

-----------------------------------
-- VRenamings of binding contexts --
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

renΓΓ⟨τ'⟩-τ : ∀ {Γ τ τ'} → τ ≤ τ' → VRen Γ (Γ ⟨ τ' ⟩ -ᶜ τ)
renΓΓ⟨τ'⟩-τ {Γ} {τ} {τ'} p = ⟨⟩-≤-ren p -ʳ τ ∘ʳ ⟨⟩-ᶜ-ren' τ

-- weakening lemma 

-ᶜ-++ᶜ-wk-ren : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → VRen Γ (Γ ++ᶜ Γ' -ᶜ τ)
-ᶜ-++ᶜ-wk-ren {Γ} {Γ'} {τ} p = (eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ∘ʳ wk-ctx-ren

-- -ᶜ for joined contexts lemmas

Γ⋈Δ-ᶜτ : ∀ {Γ Δ τ} → τ ≤ ctx-time (BCtx→Ctx Δ) → VRen Γ (Γ ⋈ Δ -ᶜ τ)
Γ⋈Δ-ᶜτ {Γ} {Δ} {τ} p = eq-ren (sym (Γ⋈Δ≡Γ++ᶜctxΔ Γ Δ)) -ʳ τ ∘ʳ -ᶜ-++ᶜ-wk-ren p

-- rename time to context

ren⟨τ⟩-ctx : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → VRen (Γ ⟨ τ ⟩) (Γ ++ᶜ Γ')
ren⟨τ⟩-ctx {Γ} {[]} {.zero} z≤n = ⟨⟩-η-ren
ren⟨τ⟩-ctx {Γ} {Γ' ∷ X} {τ} p = wk-ren ∘ʳ ren⟨τ⟩-ctx p
ren⟨τ⟩-ctx {Γ} {Γ' ⟨ τ' ⟩} {τ} p with τ ≤? τ'
... | yes q = cong-⟨⟩-ren wk-ctx-ren ∘ʳ (⟨⟩-≤-ren q) 
... | no ¬q = 
        (cong-⟨⟩-ren (ren⟨τ⟩-ctx (m≤n+k⇒m∸k≤n τ (ctx-time Γ') τ' p)) 
            ∘ʳ ⟨⟩-μ-ren {τ = τ ∸ τ'}) 
        ∘ʳ +-∸-id-ren τ τ'

-- elim nonused variables from the joined contex 

renΓ⟨τ⟩-Γ⋈Δ : ∀ {Γ Δ A τ} → τ ≤ ctx-time (BCtx→Ctx Δ) → VRen (Γ ⟨ τ ⟩) (Γ ∷ A ⋈ Δ)
renΓ⟨τ⟩-Γ⋈Δ {Γ} {Δ} {A} {τ} p = 
    ((eq-ren (sym (Γ⋈Δ≡Γ++ᶜctxΔ (Γ ∷ A) Δ))) 
    ∘ʳ cong-ren wk-ren) 
    ∘ʳ ren⟨τ⟩-ctx p 

ren-++-⋈ : ∀ {Γ Δ Γ'} → BCtx→Ctx Δ ≡ Γ' → VRen (Γ ++ᶜ Γ') (Γ ⋈ Δ)
ren-++-⋈ {Γ} {Δ} {Γ'} p = eq-ren (sym (trans (Γ⋈Δ≡Γ++ᶜctxΔ Γ Δ) (++ᶜ-inj Γ (BCtx→Ctx Δ) Γ' p)))



-}
 
