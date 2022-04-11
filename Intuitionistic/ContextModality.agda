---------------------------------------------------
-- Admissible rules for the context modality ⟨_⟩ --
---------------------------------------------------

-- NOTE: This file is likely going to be obsolete with the
-- new definition of variable renamings in Renamings.agda

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language

module ContextModality where

{-

-- Time-ordering of contexts (accumulated monotonicity of ⟨_⟩s)
---------------------------------------------------------------

data _≤ᶜ_ : Ctx → Ctx → Set where
  ≤-[] : [] ≤ᶜ []
  ≤-∷ᶜ : ∀ {Γ Γ' A} → Γ ≤ᶜ Γ' → Γ ∷ᶜ A ≤ᶜ Γ' ∷ᶜ A
  ≤-⟨⟩ : ∀ {Γ Γ' τ τ'} → Γ ≤ᶜ Γ' → τ ≤ τ' → Γ ⟨ τ ⟩ ≤ᶜ Γ' ⟨ τ' ⟩

≤ᶜ-refl : ∀ {Γ} → Γ ≤ᶜ Γ
≤ᶜ-refl {[]}      = ≤-[]
≤ᶜ-refl {Γ ∷ᶜ A}  = ≤-∷ᶜ ≤ᶜ-refl
≤ᶜ-refl {Γ ⟨ τ ⟩} = ≤-⟨⟩ ≤ᶜ-refl ≤-refl

≤ᶜ-reflexive : ∀ {Γ Γ'} → Γ ≡ Γ' → Γ ≤ᶜ Γ'
≤ᶜ-reflexive refl = ≤ᶜ-refl

-- ≤ᶜ implies ordering on ctx-delays

≤ᶜ-ctx-delay : ∀ {Γ Γ'} → Γ ≤ᶜ Γ' → ctx-delay Γ ≤ ctx-delay Γ'
≤ᶜ-ctx-delay ≤-[] = ≤-refl
≤ᶜ-ctx-delay (≤-∷ᶜ p) = ≤ᶜ-ctx-delay p
≤ᶜ-ctx-delay (≤-⟨⟩ p q) = +-mono-≤ (≤ᶜ-ctx-delay p) q

-- Interaction between context splitting and ≤ᶜ

split-≤ᶜ : ∀ {Γ Γ' Γ₁ Γ₂}
         → Γ₁ , Γ₂ split Γ
         → Γ ≤ᶜ Γ'
         → Σ[ Γ₁' ∈ Ctx ] Σ[ Γ₂' ∈ Ctx ]
             (Γ₁' , Γ₂' split Γ' × Γ₁ ≤ᶜ Γ₁' × Γ₂ ≤ᶜ Γ₂')

split-≤ᶜ split-[] q = _ , [] , split-[] , q , ≤-[]
split-≤ᶜ (split-∷ᶜ p) (≤-∷ᶜ q) with split-≤ᶜ p q
... | Γ₁' , Γ₂' , p' , q' , r' = Γ₁' , Γ₂' ∷ᶜ _ , split-∷ᶜ p' , q' , ≤-∷ᶜ r'
split-≤ᶜ (split-⟨⟩ p) (≤-⟨⟩ q r) with split-≤ᶜ p q
... | Γ₁' , Γ₂' , p' , q' , r' = Γ₁' , Γ₂' ⟨ _ ⟩ , split-⟨⟩ p' , q' , ≤-⟨⟩ r' r

-- Interaction between context splitting and ++ᶜ 

split-≡ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → Γ₁ ++ᶜ Γ₂ ≡ Γ
split-≡ split-[] = refl
split-≡ (split-∷ᶜ p) = cong (_∷ᶜ _) (split-≡ p)
split-≡ (split-⟨⟩ p) = cong (_⟨ _ ⟩) (split-≡ p)

≡-split : ∀ {Γ Γ₁ Γ₂} → Γ₁ ++ᶜ Γ₂ ≡ Γ → Γ₁ , Γ₂ split Γ
≡-split {Γ₂ = []}       refl = split-[]
≡-split {Γ₂ = Γ₂ ∷ᶜ A}  refl = split-∷ᶜ (≡-split refl)
≡-split {Γ₂ = Γ₂ ⟨ τ ⟩} refl = split-⟨⟩ (≡-split refl)

split-≡-++ᶜ : ∀ {Γ₁ Γ₂} → Γ₁ , Γ₂ split (Γ₁ ++ᶜ Γ₂)
split-≡-++ᶜ = ≡-split refl

-- ≤ᶜ preserves ∈

∈-≤ᶜ-∈ : ∀ {A Γ Γ'} → A ∈ Γ → Γ ≤ᶜ Γ' → A ∈ Γ'
∈-≤ᶜ-∈ Hd (≤-∷ᶜ q) = Hd
∈-≤ᶜ-∈ (Tl p) (≤-∷ᶜ q) = Tl (∈-≤ᶜ-∈ p q)

-- Well-typed terms are monotonic with respect to ≤ᶜ

mutual

  ⊢V⦂-ctx-monotonic : ∀ {Γ Γ' A}
                    → Γ ≤ᶜ Γ'
                    → Γ ⊢V⦂ A
                    ------------
                    → Γ' ⊢V⦂ A

  ⊢V⦂-ctx-monotonic p (var x)   = var (∈-≤ᶜ-∈ x p)
  ⊢V⦂-ctx-monotonic p (const c) = const c
  ⊢V⦂-ctx-monotonic p ⋆         = ⋆
  ⊢V⦂-ctx-monotonic p (lam M)   = lam (⊢C⦂-ctx-monotonic (≤-∷ᶜ p) M)
  ⊢V⦂-ctx-monotonic p (box V)   = box (⊢V⦂-ctx-monotonic (≤-⟨⟩ p ≤-refl) V)

  ⊢C⦂-ctx-monotonic : ∀ {Γ Γ' C}
                    → Γ ≤ᶜ Γ'
                    → Γ ⊢C⦂ C
                    ------------
                    → Γ' ⊢C⦂ C

  ⊢C⦂-ctx-monotonic p (return V) = return (⊢V⦂-ctx-monotonic p V)
  ⊢C⦂-ctx-monotonic p (M ; N)    = ⊢C⦂-ctx-monotonic p M ; ⊢C⦂-ctx-monotonic (≤-∷ᶜ p) N
  ⊢C⦂-ctx-monotonic p (V · W)    = ⊢V⦂-ctx-monotonic p V · ⊢V⦂-ctx-monotonic p W
  ⊢C⦂-ctx-monotonic p (absurd V) = absurd (⊢V⦂-ctx-monotonic p V)
  ⊢C⦂-ctx-monotonic p (perform op V M) =
    perform op (⊢V⦂-ctx-monotonic p V) (⊢C⦂-ctx-monotonic (≤-∷ᶜ (≤-⟨⟩ p ≤-refl)) M)
  ⊢C⦂-ctx-monotonic p (unbox q r V M) with split-≤ᶜ q p
  ... | (Γ₁' ⟨ τ' ⟩) , Γ₂' , p' , ≤-⟨⟩ q' q'' , r' =
    unbox p'
      (≤-trans r (+-mono-≤ q'' (≤ᶜ-ctx-delay r')))
      (⊢V⦂-ctx-monotonic q' V)
      (⊢C⦂-ctx-monotonic (≤-∷ᶜ p) M)
  ⊢C⦂-ctx-monotonic p (coerce q M) = coerce q (⊢C⦂-ctx-monotonic p M)


-- Strengthening context with ⟨ 0 ⟩ (the graded monadic unit of ⟨_⟩)
--------------------------------------------------------------------

⟨⟩-strengthen-var : ∀ {Γ Γ' Γ₁ Γ₂ A}
                  → Γ ≡ (Γ₁ ⟨ 0 ⟩) ++ᶜ Γ₂ → Γ' ≡ Γ₁ ++ᶜ Γ₂ → A ∈ Γ → A ∈ Γ'
⟨⟩-strengthen-var {Γ₂ = Γ₂ ∷ᶜ _} refl refl Hd     = Hd
⟨⟩-strengthen-var {Γ₂ = Γ₂ ∷ᶜ _} refl refl (Tl x) = Tl (⟨⟩-strengthen-var refl refl x)

-- TODO: wip proof commented out for time being to work on other files

postulate

  ⊢V⦂-⟨⟩-eta : ∀ {Γ Γ' Γ₁ Γ₂ A}
            → Γ₁ ⟨ 0 ⟩ , Γ₂ split Γ
            → Γ₁ , Γ₂ split Γ'
            → Γ ⊢V⦂ A
            -----------------------
            → Γ' ⊢V⦂ A

  ⊢C⦂-⟨⟩-eta : ∀ {Γ Γ' Γ₁ Γ₂ C}
            → Γ₁ ⟨ 0 ⟩ , Γ₂ split Γ
            → Γ₁ , Γ₂ split Γ'
            → Γ ⊢C⦂ C
            -----------------------
            → Γ' ⊢C⦂ C

{-
mutual

  ⊢V⦂-⟨⟩-strengthen : ∀ {Γ Γ' Γ₁ Γ₂ A}
                    → Γ₁ ⟨ 0 ⟩ , Γ₂ split Γ
                    → Γ₁ , Γ₂ split Γ'
                    → Γ ⊢V⦂ A
                    -----------------------
                    → Γ' ⊢V⦂ A

  ⊢V⦂-⟨⟩-strengthen p q (var x) =
    var (⟨⟩-strengthen-var (sym (split-≡ p)) (sym (split-≡ q)) x)
  ⊢V⦂-⟨⟩-strengthen p q (const c) = const c
  ⊢V⦂-⟨⟩-strengthen p q ⋆ = ⋆
  ⊢V⦂-⟨⟩-strengthen p q (lam M) =
    lam (⊢C⦂-⟨⟩-strengthen (split-∷ᶜ p) (split-∷ᶜ q) M)
  ⊢V⦂-⟨⟩-strengthen p q (box V) =
    box (⊢V⦂-⟨⟩-strengthen (split-⟨⟩ p) (split-⟨⟩ q) V)

  ⊢C⦂-⟨⟩-strengthen : ∀ {Γ Γ' Γ₁ Γ₂ C}
                    → Γ₁ ⟨ 0 ⟩ , Γ₂ split Γ
                    → Γ₁ , Γ₂ split Γ'
                    → Γ ⊢C⦂ C
                    -----------------------
                    → Γ' ⊢C⦂ C

  ⊢C⦂-⟨⟩-strengthen p q (return V) =
    return (⊢V⦂-⟨⟩-strengthen p q V)
  ⊢C⦂-⟨⟩-strengthen p q (M ; N) =
    ⊢C⦂-⟨⟩-strengthen p q M ; ⊢C⦂-⟨⟩-strengthen (split-∷ᶜ p) (split-∷ᶜ q) N
  ⊢C⦂-⟨⟩-strengthen p q (V · W) =
    ⊢V⦂-⟨⟩-strengthen p q V · ⊢V⦂-⟨⟩-strengthen p q W
  ⊢C⦂-⟨⟩-strengthen p q (absurd V) =
    absurd (⊢V⦂-⟨⟩-strengthen p q V)
  ⊢C⦂-⟨⟩-strengthen p q (perform op V M) =
    perform op
      (⊢V⦂-⟨⟩-strengthen p q V)
      (⊢C⦂-⟨⟩-strengthen (split-∷ᶜ (split-⟨⟩ p)) (split-∷ᶜ (split-⟨⟩ q)) M)
  ⊢C⦂-⟨⟩-strengthen p q (unbox r s V M) = 
    unbox {!!} {!!} {!!} (⊢C⦂-⟨⟩-strengthen (split-∷ᶜ p) (split-∷ᶜ q) M)
  ⊢C⦂-⟨⟩-strengthen p q (coerce r M) =
    coerce r (⊢C⦂-⟨⟩-strengthen p q M)
-}

-- Merging two ⟨_⟩s (the graded monadic multiplication of ⟨_⟩)
--------------------------------------------------------------

-- TODO: write up the proofs of this

postulate

  ⊢V⦂-⟨⟩-mu : ∀ {Γ Γ' Γ₁ Γ₂ τ τ' A}
           → Γ₁ ⟨ τ + τ' ⟩ , Γ₂ split Γ
           → Γ₁ ⟨ τ ⟩ ⟨ τ' ⟩ , Γ₂ split Γ'
           → Γ ⊢V⦂ A
           -------------------------------
           → Γ' ⊢V⦂ A

  ⊢C⦂-⟨⟩-mu : ∀ {Γ Γ' Γ₁ Γ₂ τ τ' C}
           → Γ₁ ⟨ τ + τ' ⟩ , Γ₂ split Γ
           → Γ₁ ⟨ τ ⟩ ⟨ τ' ⟩ , Γ₂ split Γ'
           → Γ ⊢C⦂ C
           -------------------------------
           → Γ' ⊢C⦂ C

-}
