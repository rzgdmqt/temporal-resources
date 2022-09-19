---------------------------------------------------------
-- Environment splitting morphisms form an isomorphism --
---------------------------------------------------------

open import Semantics.Model

module Semantics.Interpretation.Properties.split-env-isomorphism (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

split-env-split-env⁻¹-iso : ∀ {Γ Γ' Γ'' A}
                          → (p : Γ' , Γ'' split Γ)
                          → split-env⁻¹ p ∘ᵐ split-env p
                          ≡ idᵐ {⟦ Γ ⟧ᵉᵒ A}

split-env-split-env⁻¹-iso split-[] = 
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
split-env-split-env⁻¹-iso (split-∷ p) = 
  begin
       ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
    ⟨ (split-env⁻¹ p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
      (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
       (begin
         fstᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)) ⟩
         idᵐ ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congˡ (sym (split-env-split-env⁻¹-iso p)) ⟩
         (split-env⁻¹ p ∘ᵐ split-env p) ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         split-env⁻¹ p ∘ᵐ split-env p ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
         split-env⁻¹ p ∘ᵐ fstᵐ ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (split-env⁻¹ p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)
       (begin
         sndᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) ⟩
         idᵐ ∘ᵐ idᵐ ∘ᵐ sndᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
         idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)) ⟩
    idᵐ
  ∎
split-env-split-env⁻¹-iso (split-⟨⟩ {τ = τ} p) = 
  begin
    ⟨ τ ⟩ᶠ (split-env⁻¹ p) ∘ᵐ ⟨ τ ⟩ᶠ (split-env p)
  ≡⟨ sym (⟨⟩-∘ᵐ _ _) ⟩
    ⟨ τ ⟩ᶠ (split-env⁻¹ p ∘ᵐ split-env p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env-split-env⁻¹-iso p) ⟩
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎

split-env⁻¹-split-env-iso : ∀ {Γ Γ' Γ'' A}
                          → (p : Γ' , Γ'' split Γ)
                          → split-env p ∘ᵐ split-env⁻¹ p
                          ≡ idᵐ {⟦ Γ'' ⟧ᵉᵒ (⟦ Γ' ⟧ᵉᵒ A)}

split-env⁻¹-split-env-iso split-[] = 
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
split-env⁻¹-split-env-iso (split-∷ p) = 
  begin
       ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
    ⟨ (split-env p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
      (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
       (begin
         fstᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)) ⟩
         idᵐ ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congˡ (sym (split-env⁻¹-split-env-iso p)) ⟩
         (split-env p ∘ᵐ split-env⁻¹ p) ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         split-env p ∘ᵐ split-env⁻¹ p ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
         split-env p ∘ᵐ fstᵐ ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (split-env p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)
       (begin
         sndᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) ⟩
         idᵐ ∘ᵐ idᵐ ∘ᵐ sndᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
         idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)) ⟩
    idᵐ
  ∎
split-env⁻¹-split-env-iso (split-⟨⟩ {τ = τ} p) = 
  begin
    ⟨ τ ⟩ᶠ (split-env p) ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ p)
  ≡⟨ sym (⟨⟩-∘ᵐ _ _) ⟩
    ⟨ τ ⟩ᶠ (split-env p ∘ᵐ split-env⁻¹ p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env⁻¹-split-env-iso p) ⟩
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎
