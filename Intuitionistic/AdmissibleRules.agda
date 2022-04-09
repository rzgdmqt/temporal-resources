-------------------------------------------------------
-- Some rules that are admissible in the type system --
-------------------------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language

module AdmissibleRules where

-- Time-ordering of contexts (accumulated monotonicity of ⟨_⟩s)

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

split-≡-++ᶜ : ∀ {Γ₁ Γ₂} → Γ₁ , Γ₂ split (Γ₁ ++ᶜ Γ₂)
split-≡-++ᶜ {Γ₂ = []}       = split-[]
split-≡-++ᶜ {Γ₂ = Γ₂ ∷ᶜ A}  = split-∷ᶜ split-≡-++ᶜ
split-≡-++ᶜ {Γ₂ = Γ₂ ⟨ τ ⟩} = split-⟨⟩ split-≡-++ᶜ

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
  ⊢V⦂-ctx-monotonic p ⟨⟩        = ⟨⟩
  ⊢V⦂-ctx-monotonic p (lam M)   = lam (⊢C⦂-ctx-monotonic (≤-∷ᶜ p) M)
  ⊢V⦂-ctx-monotonic p (box V)   = box (⊢V⦂-ctx-monotonic (≤-⟨⟩ p ≤-refl) V)

  ⊢C⦂-ctx-monotonic : ∀ {Γ Γ' C}
                    → Γ ≤ᶜ Γ'
                    → Γ ⊢C⦂ C
                    ------------
                    → Γ' ⊢C⦂ C

  ⊢C⦂-ctx-monotonic p (return V)       = return (⊢V⦂-ctx-monotonic p V)
  ⊢C⦂-ctx-monotonic p (M ; N)          = ⊢C⦂-ctx-monotonic p M ; ⊢C⦂-ctx-monotonic (≤-∷ᶜ p) N
  ⊢C⦂-ctx-monotonic p (V · W)          = ⊢V⦂-ctx-monotonic p V · ⊢V⦂-ctx-monotonic p W
  ⊢C⦂-ctx-monotonic p (absurd V)       = absurd (⊢V⦂-ctx-monotonic p V)
  ⊢C⦂-ctx-monotonic p (perform op V M) =
    perform op (⊢V⦂-ctx-monotonic p V) (⊢C⦂-ctx-monotonic (≤-∷ᶜ (≤-⟨⟩ p ≤-refl)) M)
  ⊢C⦂-ctx-monotonic p (unbox V q r) with split-≤ᶜ q p
  ... | Γ₁' , Γ₂' , p' , q' , r' rewrite sym (split-≡ p') =
    unbox (⊢V⦂-ctx-monotonic q' V) (split-≡-++ᶜ {Γ₁'} {Γ₂'}) (≤-trans r (≤ᶜ-ctx-delay r'))  
  ⊢C⦂-ctx-monotonic p (coerce q M)     = coerce q (⊢C⦂-ctx-monotonic p M)
