-------------------------------------------------------------------------
-- Environment splitting morphisms interaction with equality renamings --
-------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.split-env-eq-ren (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Semantics.Interpretation.Properties.split-env-isomorphism Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

-- Auxiliary lemmas relating renamings with equality congruences

eq-ren-cong-fstᵐ : ∀ {Γ Γ' Γ'' A B}
                 → (p : Γ ++ᶜ Γ' ≡ Γ'')
                 → fstᵐ ∘ᵐ ⟦ eq-ren (cong (_∷ A) p) ⟧ʳ {B}
                 ≡ ⟦ eq-ren p ⟧ʳ ∘ᵐ fstᵐ

eq-ren-cong-fstᵐ refl = 
  begin
    fstᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ fstᵐ
  ∎

eq-ren-cong-fstᵐ-sym : ∀ {Γ Γ' Γ'' A B}
                     → (p : Γ'' ≡ Γ ++ᶜ Γ')
                     → fstᵐ ∘ᵐ ⟦ eq-ren (cong (_∷ A) p) ⟧ʳ {B}
                     ≡ ⟦ eq-ren p ⟧ʳ ∘ᵐ fstᵐ

eq-ren-cong-fstᵐ-sym refl = 
  begin
    fstᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ fstᵐ
  ∎

eq-ren-cong-sndᵐ : ∀ {Γ Γ' Γ'' A B}
                 → (p : Γ ++ᶜ Γ' ≡ Γ'')
                 → sndᵐ ∘ᵐ ⟦ eq-ren (cong (_∷ A) p) ⟧ʳ {B}
                 ≡ sndᵐ

eq-ren-cong-sndᵐ refl = 
  begin
    sndᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    sndᵐ
  ∎

eq-ren-cong-sndᵐ-sym : ∀ {Γ Γ' Γ'' A B}
                     → (p : Γ'' ≡ Γ ++ᶜ Γ')
                     → sndᵐ ∘ᵐ ⟦ eq-ren (cong (_∷ A) p) ⟧ʳ {B}
                     ≡ sndᵐ

eq-ren-cong-sndᵐ-sym refl = 
  begin
    sndᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    sndᵐ
  ∎

eq-ren-⟨⟩ : ∀ {Γ Γ' Γ'' τ B}
          → (p : Γ ++ᶜ Γ' ≡ Γ'')
          → ⟨ τ ⟩ᶠ (⟦ eq-ren p ⟧ʳ)
          ≡ ⟦ eq-ren (cong (_⟨ τ ⟩) p) ⟧ʳ {B}

eq-ren-⟨⟩ {τ = τ} refl = 
  begin
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎

eq-ren-⟨⟩-sym : ∀ {Γ Γ' Γ'' τ B}
              → (p : Γ'' ≡ Γ ++ᶜ Γ')
              → ⟨ τ ⟩ᶠ (⟦ eq-ren p ⟧ʳ)
              ≡ ⟦ eq-ren (cong (_⟨ τ ⟩) p) ⟧ʳ {B}

eq-ren-⟨⟩-sym {τ = τ} refl = 
  begin
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎


-- Environment splitting morphisms interaction with equality renamings

split-env-eq-ren : ∀ {Γ Γ' Γ'' A}
                 → (p : Γ' , Γ'' split Γ)
                 → split-env p {A}
                 ≡    split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl)
                   ∘ᵐ ⟦ eq-ren (split-≡ p) ⟧ʳ

split-env-eq-ren {Γ} {.Γ} {.[]} split-[] = 
  begin
    idᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ idᵐ
  ∎
split-env-eq-ren {.(_ ∷ _)} {Γ'} {Γ'' ∷ A} (split-∷ p) = 
  begin
    ⟨ split-env p ∘ᵐ fstᵐ
    ,
      idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ cong ⟨_, idᵐ ∘ᵐ sndᵐ ⟩ᵐ (∘ᵐ-congˡ (split-env-eq-ren p)) ⟩
    ⟨    (   split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl)
          ∘ᵐ ⟦ eq-ren (split-≡ p) ⟧ʳ)
      ∘ᵐ fstᵐ
    ,
      idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
       (trans (∘ᵐ-assoc _ _ _)
         (trans (∘ᵐ-congʳ (sym (eq-ren-cong-fstᵐ {Γ = Γ'} {Γ' = Γ''} {A = A} (split-≡ p)))) (sym (∘ᵐ-assoc _ _ _))))
       (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (eq-ren-cong-sndᵐ {Γ = Γ'} {Γ' = Γ''} {A = A} (split-≡ p))))) ⟩
    ⟨   (   split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl)
         ∘ᵐ fstᵐ)
     ∘ᵐ ⟦ eq-ren (cong (_∷ A) (split-≡ p)) ⟧ʳ
    ,
        (idᵐ ∘ᵐ sndᵐ)
     ∘ᵐ ⟦ eq-ren (cong (_∷ A) (split-≡ p)) ⟧ʳ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       ⟨    split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl)
         ∘ᵐ fstᵐ
       ,
            idᵐ
         ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟦ eq-ren (cong (_∷ A) (split-≡ p)) ⟧ʳ
  ∎
split-env-eq-ren {.(_ ⟨ _ ⟩)} {Γ'} {Γ'' ⟨ τ ⟩} (split-⟨⟩ p) = 
  begin
    ⟨ τ ⟩ᶠ (split-env p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env-eq-ren p) ⟩
    ⟨ τ ⟩ᶠ (split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ ⟦ eq-ren (split-≡ p) ⟧ʳ)
  ≡⟨ ⟨⟩-∘ᵐ _ _ ⟩
       ⟨ τ ⟩ᶠ (split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
    ∘ᵐ ⟨ τ ⟩ᶠ (⟦ eq-ren (split-≡ p) ⟧ʳ)
  ≡⟨ ∘ᵐ-congʳ (eq-ren-⟨⟩ {Γ = Γ'} {Γ' = Γ''} (split-≡ p)) ⟩
       ⟨ τ ⟩ᶠ (split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
    ∘ᵐ ⟦ eq-ren (cong (_⟨ τ ⟩) (split-≡ p)) ⟧ʳ
  ∎


split-env⁻¹-eq-ren : ∀ {Γ Γ' Γ'' A}
                   → (p : Γ' , Γ'' split Γ)
                   → split-env⁻¹ p {A}
                   ≡    ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
                     ∘ᵐ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl)
                     
split-env⁻¹-eq-ren {Γ} {.Γ} {.[]} {A} split-[] = 
  begin
    idᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ idᵐ
  ∎
split-env⁻¹-eq-ren {.(_ ∷ _)} {Γ'} {Γ'' ∷ B} {A} (split-∷ p) = 
  begin
    ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
      (begin
           fstᵐ
        ∘ᵐ ⟦ eq-ren (sym (cong (_∷ B) (split-≡ p))) ⟧ʳ
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   fstᵐ
            ∘ᵐ ⟦ eq-ren (sym (cong (_∷ B) (split-≡ p))) ⟧ʳ)
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ
          (cong (λ p → ⟦ eq-ren p ⟧ʳ) {(sym (cong (_∷ B) (split-≡ p)))} {(cong (_∷ B) (sym (split-≡ p)))} uip)) ⟩
           (   fstᵐ
            ∘ᵐ ⟦ eq-ren (cong (_∷ B) (sym (split-≡ p))) ⟧ʳ)
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (eq-ren-cong-fstᵐ-sym {Γ'} {Γ''} (sym (split-≡ p))) ⟩
           (   ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
            ∘ᵐ fstᵐ)
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
        ∘ᵐ fstᵐ
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
           ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
        ∘ᵐ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl)
        ∘ᵐ fstᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
            ∘ᵐ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congˡ (sym (split-env⁻¹-eq-ren p)) ⟩
           split-env⁻¹ p
        ∘ᵐ fstᵐ
      ∎)
      (begin
           sndᵐ
        ∘ᵐ ⟦ eq-ren (sym (cong (_∷ B) (split-≡ p))) ⟧ʳ
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   sndᵐ
            ∘ᵐ ⟦ eq-ren (sym (cong (_∷ B) (split-≡ p))) ⟧ʳ)
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ
          (cong (λ p → ⟦ eq-ren p ⟧ʳ) {sym (cong (_∷ B) (split-≡ p))} {cong (_∷ B) (sym (split-≡ p))} uip)) ⟩
           (   sndᵐ
            ∘ᵐ ⟦ eq-ren (cong (_∷ B) (sym (split-≡ p))) ⟧ʳ)
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (eq-ren-cong-sndᵐ-sym {Γ'} {Γ''} (sym (split-≡ p))) ⟩
           sndᵐ
        ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ⟨⟩ᵐ-sndᵐ _ _ ⟩
           idᵐ
        ∘ᵐ sndᵐ
      ∎)) ⟩
       ⟦ eq-ren (sym (cong (_∷ B) (split-≡ p))) ⟧ʳ
    ∘ᵐ ⟨ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ∎
split-env⁻¹-eq-ren {.(_ ⟨ _ ⟩)} {Γ'} {Γ'' ⟨ τ ⟩} {A} (split-⟨⟩ p) = 
  begin
    ⟨ τ ⟩ᶠ (split-env⁻¹ p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env⁻¹-eq-ren p) ⟩
    ⟨ τ ⟩ᶠ (   ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
            ∘ᵐ split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
  ≡⟨ ⟨⟩-∘ᵐ _ _ ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (split-≡ p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
  ≡⟨ ∘ᵐ-congˡ (eq-ren-⟨⟩-sym {Γ'} {Γ''} (sym (split-≡ p))) ⟩
       ⟦ eq-ren (cong (_⟨ τ ⟩) (sym (split-≡ p))) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
  ≡⟨ ∘ᵐ-congˡ (cong (λ p → ⟦ eq-ren p ⟧ʳ) {cong (_⟨ τ ⟩) (sym (split-≡ p))}
      {sym (cong (_⟨ τ ⟩) (split-≡ p))} uip) ⟩
       ⟦ eq-ren (sym (cong (_⟨ τ ⟩) (split-≡ p))) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl))
  ∎
