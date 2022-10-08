-----------------------------------------------------------------------
-- Relating syntactic substitutions to semantic morphism composition --
-----------------------------------------------------------------------

open import Semantics.Model

module Semantics.Substitutions.Properties.VC-subst (Mod : Model) where

open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Semantics.Interpretation.Properties.env-⟨⟩-ᶜ-naturality Mod

open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-split-env-naturality Mod
open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-eq-ren-naturality Mod
open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-ren-naturality Mod
open import Semantics.Renamings.Properties.split-env-eq-ren Mod
open import Semantics.Renamings.Properties.split-env-wk-ren Mod
open import Semantics.Renamings.Properties.eq-ren Mod
open import Semantics.Renamings.Properties.var-not-in-ctx-after-ᶜ-wk-ren Mod
open import Semantics.Renamings.Properties.VC-rename Mod

open import Semantics.Substitutions.Properties.var-subst Mod
open import Semantics.Substitutions.Properties.VC-subst-aux Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

{-
postulate

-- NOTE: The code below typeckecks, but is quite slow (TODO: refactor). Thus, uncomment 
--       this postulate block when fiddlying around with the above dependencies.

  V-subst≡∘ᵐ : ∀ {Γ A B τ}
             → (V : Γ ⊢V⦂ B)
             → (x : A ∈[ τ ] Γ)
             → (W : proj₁ (var-split x) ⊢V⦂ A)
             → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
             ≡    ⟦ V ⟧ᵛᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  C-subst≡∘ᵐ : ∀ {Γ A C τ}
             → (M : Γ ⊢C⦂ C)
             → (x : A ∈[ τ ] Γ)
             → (W : proj₁ (var-split x) ⊢V⦂ A)
             → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ
             ≡    ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 
-}




-- Main substitution lemmas

mutual

  V-subst≡∘ᵐ : ∀ {Γ A B τ}
             → (V : Γ ⊢V⦂ B)
             → (x : A ∈[ τ ] Γ)
             → (W : proj₁ (var-split x) ⊢V⦂ A)
             → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
             ≡    ⟦ V ⟧ᵛᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  V-subst≡∘ᵐ (var y) x W = 
    begin
      ⟦ y [ x ↦ W ]var ⟧ᵛᵗ
    ≡⟨ var-subst≡∘ᵐ y x W ⟩
         var-in-env y
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst≡∘ᵐ (const c) x W = 
    begin
         constᵐ c
      ∘ᵐ terminalᵐ
    ≡⟨ ∘ᵐ-congʳ (sym terminalᵐ-unique) ⟩
         constᵐ c
      ∘ᵐ terminalᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (constᵐ c ∘ᵐ terminalᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst≡∘ᵐ ⋆ x W = 
    begin
      terminalᵐ
    ≡⟨ sym terminalᵐ-unique ⟩
         terminalᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst≡∘ᵐ ⦉ V₁ , V₂ ⦊ x W =
    begin
      ⟨ ⟦ V₁ [ x ↦ W ]v ⟧ᵛᵗ , ⟦ V₂ [ x ↦ W ]v ⟧ᵛᵗ ⟩ᵐ
    ≡⟨ cong₂ ⟨_,_⟩ᵐ (V-subst≡∘ᵐ V₁ x W) (V-subst≡∘ᵐ V₂ x W) ⟩
      ⟨    ⟦ V₁ ⟧ᵛᵗ
        ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
        ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
        ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ,
           ⟦ V₂ ⟧ᵛᵗ
        ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
        ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
        ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
         ⟨ ⟦ V₁ ⟧ᵛᵗ , ⟦ V₂ ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst≡∘ᵐ (lam {A = A} M) x W = 
    begin
      curryᵐ ⟦ M [ Tl-∷ x ↦ W ]c ⟧ᶜᵗ
    ≡⟨ cong curryᵐ (C-subst≡∘ᵐ M (Tl-∷ x) W) ⟩
      curryᵐ (   ⟦ M ⟧ᶜᵗ
              ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env
                   {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
                   {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
                   (≡-split refl))
    ≡⟨ cong curryᵐ (∘ᵐ-congʳ (
         trans
           (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
           (trans
             (sym (mapˣᵐ-∘ᵐ _ _ _ _))
             (cong₂ mapˣᵐ refl
               (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))))) ⟩
      curryᵐ (   ⟦ M ⟧ᶜᵗ
              ∘ᵐ mapˣᵐ
                   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                    ∘ᵐ split-env
                         {Γ' = proj₁ (var-split x)}
                         {Γ'' = proj₁ (proj₂ (var-split x))}
                         (≡-split refl))
                   idᵐ)
    ≡⟨ curryᵐ-nat _ _ ⟩
         curryᵐ ⟦ M ⟧ᶜᵗ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst≡∘ᵐ {A = A} (box {B} {τ} V) x W =
    begin
         [ τ ]ᶠ ⟦ V [ Tl-⟨⟩ x ↦ W ]v ⟧ᵛᵗ
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (V-subst≡∘ᵐ V (Tl-⟨⟩ x) W)) ⟩
         [ τ ]ᶠ (   ⟦ V ⟧ᵛᵗ
                 ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-⟨⟩ x)))))
                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-⟨⟩ x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                 ∘ᵐ split-env
                      {Γ' = proj₁ (var-split (Tl-⟨⟩ {τ = τ} x))}
                      {Γ'' = proj₁ (proj₂ (var-split (Tl-⟨⟩ x)))}
                      (≡-split refl))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congˡ ([]-∘ᵐ _ _) ⟩
         (   [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
          ∘ᵐ [ τ ]ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-⟨⟩ x)))))
                     ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-⟨⟩ x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                     ∘ᵐ split-env
                          {Γ' = proj₁ (var-split (Tl-⟨⟩ {τ = τ} x))}
                          {Γ'' = proj₁ (proj₂ (var-split (Tl-⟨⟩ x)))}
                          (≡-split refl)))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
      ∘ᵐ [ τ ]ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-⟨⟩ x)))))
                     ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-⟨⟩ x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                     ∘ᵐ split-env
                          {Γ' = proj₁ (var-split (Tl-⟨⟩ {τ = τ} x))}
                          {Γ'' = proj₁ (proj₂ (var-split (Tl-⟨⟩ x)))}
                          (≡-split refl))
      ∘ᵐ η⊣
    ≡⟨⟩
         [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
      ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                 ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                 ⟨ τ ⟩ᶠ (split-env
                          {Γ' = proj₁ (var-split x)}
                          {Γ'' = proj₁ (proj₂ (var-split x))}
                          (≡-split refl)))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (sym
        (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))))) ⟩
         [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
      ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                         ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                         ∘ᵐ split-env
                              {Γ' = proj₁ (var-split x)}
                              {Γ'' = proj₁ (proj₂ (var-split x))}
                              (≡-split refl)))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (η⊣-nat _) ⟩
         [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
      ∘ᵐ η⊣
      ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
    ≡⟨⟩
         [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
      ∘ᵐ η⊣
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   [ τ ]ᶠ ⟦ V ⟧ᵛᵗ
          ∘ᵐ η⊣)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎

  C-subst≡∘ᵐ : ∀ {Γ A C τ}
             → (M : Γ ⊢C⦂ C)
             → (x : A ∈[ τ ] Γ)
             → (W : proj₁ (var-split x) ⊢V⦂ A)
             → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ
             ≡    ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  C-subst≡∘ᵐ (return V) x W = 
    begin
         ηᵀ
      ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-subst≡∘ᵐ V x W) ⟩
         ηᵀ
      ∘ᵐ ⟦ V ⟧ᵛᵗ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (_;_ {A = A} {τ = τ} M N) x W =
    begin
         μᵀ
      ∘ᵐ Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ η⊣ ,_⟩ᵐ (C-subst≡∘ᵐ M x W)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (C-subst≡∘ᵐ N (Tl-∷ (Tl-⟨⟩ x)) W))) ⟩
         μᵀ
      ∘ᵐ Tᶠ (   ⟦ N ⟧ᶜᵗ
             ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x))))))
             ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x)))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
             ∘ᵐ split-env
                  {Γ' = proj₁ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ {τ = τ} x)))}
                  {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x))))}
                  (≡-split refl))
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)) ⟩
         μᵀ
      ∘ᵐ (   Tᶠ ⟦ N ⟧ᶜᵗ
          ∘ᵐ Tᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x))))))
                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x)))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                 ∘ᵐ split-env
                      {Γ' = proj₁ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ {τ = τ} x)))}
                      {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x))))}
                      (≡-split refl)))
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ Tᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x))))))
             ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x)))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
             ∘ᵐ split-env
                  {Γ' = proj₁ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ {τ = τ} x)))}
                  {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} (Tl-⟨⟩ x))))}
                  (≡-split refl))
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ
        (trans
          (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
          (sym (mapˣᵐ-∘ᵐ _ _ _ _)))))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ Tᶠ (mapˣᵐ
              (   ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
               ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
               ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
              (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ))
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ (   Tᶠ (mapˣᵐ
                  (   ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                   ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                   ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                  (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ))
          ∘ᵐ strᵀ)
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym (strᵀ-nat _ _)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ (   strᵀ
          ∘ᵐ mapˣᵐ
               ([ τ ]ᶠ (   ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                        ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                        ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
               (Tᶠ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)))
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ mapˣᵐ
           ([ τ ]ᶠ (   ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                    ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                    ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
           (Tᶠ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ))
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨   (  [ τ ]ᶠ (⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                        ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                        ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
             ∘ᵐ fstᵐ)
          ∘ᵐ ⟨ η⊣ ,
                 ⟦ M ⟧ᶜᵗ
              ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
          ,
             (Tᶠ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ)
          ∘ᵐ ⟨ η⊣ ,
                 ⟦ M ⟧ᶜᵗ
              ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ ⟨_,_⟩ᵐ
          (∘ᵐ-assoc _ _ _)
          (∘ᵐ-assoc _ _ _)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨   [ τ ]ᶠ (⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                     ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                     ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
          ∘ᵐ fstᵐ
          ∘ᵐ ⟨ η⊣ ,
                 ⟦ M ⟧ᶜᵗ
              ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
          ,
             Tᶠ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
          ∘ᵐ sndᵐ
          ∘ᵐ ⟨ η⊣ {τ = τ} ,
                 ⟦ M ⟧ᶜᵗ
              ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨   [ τ ]ᶠ (⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                     ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                     ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
          ∘ᵐ η⊣
          ,
             Tᶠ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
          ∘ᵐ ⟦ M ⟧ᶜᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (cong₂ ⟨_,_⟩ᵐ
          (∘ᵐ-congˡ (cong [ τ ]ᶠ (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))))
          (∘ᵐ-congˡ (trans (cong Tᶠ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) T-idᵐ))))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨   [ τ ]ᶠ (⟨ τ ⟩ᶠ (   (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                             ∘ᵐ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                             ∘ᵐ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
          ∘ᵐ η⊣
          ,
             idᵐ
          ∘ᵐ ⟦ M ⟧ᶜᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (η⊣-nat _) (∘ᵐ-identityˡ _)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨   η⊣
          ∘ᵐ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
          ∘ᵐ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
          ∘ᵐ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)) ,
             ⟦ M ⟧ᶜᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
         (μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (V · V') x W =
    begin
         uncurryᵐ idᵐ
      ∘ᵐ ⟨ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ , ⟦ V' [ x ↦ W ]v ⟧ᵛᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (V-subst≡∘ᵐ V x W) (V-subst≡∘ᵐ V' x W)) ⟩
         uncurryᵐ idᵐ
      ∘ᵐ ⟨   ⟦ V ⟧ᵛᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             ⟦ V' ⟧ᵛᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
         uncurryᵐ idᵐ
      ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ V' ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   uncurryᵐ idᵐ
          ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ V' ⟧ᵛᵗ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (match V `in M) x W =
    begin
         ⟦ M [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ , ⟦ V [ x ↦ W ]v ⟧ᵛᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (V-subst≡∘ᵐ V x W))) ⟩
         ⟦ M [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ,
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (C-subst≡∘ᵐ M (Tl-∷ (Tl-∷ x)) W) ⟩
         (  ⟦ M ⟧ᶜᵗ
         ∘ᵐ ⟨    ⟨ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))) ∘ᵐ fstᵐ ,
                   idᵐ ∘ᵐ sndᵐ ⟩ᵐ
              ∘ᵐ fstᵐ ,
              idᵐ ∘ᵐ sndᵐ ⟩ᵐ
         ∘ᵐ ⟨    ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ ,
                   idᵐ ∘ᵐ sndᵐ ⟩ᵐ
              ∘ᵐ fstᵐ ,
              idᵐ ∘ᵐ sndᵐ ⟩ᵐ
         ∘ᵐ ⟨    ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ ,
                   idᵐ ∘ᵐ sndᵐ ⟩ᵐ
              ∘ᵐ fstᵐ ,
              idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ,
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ mapˣᵐ (mapˣᵐ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ) idᵐ
      ∘ᵐ mapˣᵐ (mapˣᵐ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) idᵐ) idᵐ
      ∘ᵐ mapˣᵐ (mapˣᵐ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)) idᵐ) idᵐ
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ,
               ⟦ V ⟧ᵛᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))))
        (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))) (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
          (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)) (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
            (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))))
              (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))) (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))
                (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (cong₂ ⟨_,_⟩ᵐ
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (sym (trans (⟨⟩ᵐ-fstᵐ _ _)
                    (trans (∘ᵐ-identityˡ _) (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
                      (trans (⟨⟩ᵐ-fstᵐ _ _) (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                        (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityʳ _))))))))))))))
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                    (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                          (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))))))))))))))))))))
            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (sym
              (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _)
                (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))))))))))))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨    idᵐ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ,
              ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (absurd V) x W =
    begin
         initialᵐ
      ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-subst≡∘ᵐ V x W) ⟩
         initialᵐ
      ∘ᵐ ⟦ V ⟧ᵛᵗ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (perform op V M) x W =
    begin
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ
        (cong₂ ⟨_,_⟩ᵐ
          (∘ᵐ-congʳ (V-subst≡∘ᵐ V x W))
          (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (C-subst≡∘ᵐ M (Tl-∷ (Tl-⟨⟩ x)) W)))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                       ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = type-of-gtype (arity op)} (Tl-⟨⟩ x))))))
                                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = type-of-gtype (arity op)} (Tl-⟨⟩ x)))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                       ∘ᵐ split-env
                                            {Γ' = proj₁ (var-split (Tl-∷ {B = type-of-gtype (arity op)} (Tl-⟨⟩ {τ = op-time op} x)))}
                                            {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = type-of-gtype (arity op)} (Tl-⟨⟩ x))))}
                                            (≡-split refl)))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ
        (cong₂ ⟨_,_⟩ᵐ refl
          (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
            (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _))))))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                       ∘ᵐ mapˣᵐ
                                            (⟨ op-time op ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                                             ⟨ op-time op ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                                             ⟨ op-time op ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                                            (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ
          (cong₂ mapˣᵐ refl (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ (   ⟦ M ⟧ᶜᵗ
                                       ∘ᵐ mapˣᵐ
                                            (⟨ op-time op ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                                             ⟨ op-time op ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                                             ⟨ op-time op ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                                            idᵐ))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong [ op-time op ]ᶠ (curryᵐ-nat _ _))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (   curryᵐ ⟦ M ⟧ᶜᵗ
                               ∘ᵐ ⟨ op-time op ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                               ∘ᵐ ⟨ op-time op ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                               ∘ᵐ ⟨ op-time op ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ (   [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
               ∘ᵐ [ op-time op ]ᶠ (   ⟨ op-time op ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                                   ∘ᵐ ⟨ op-time op ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                                   ∘ᵐ ⟨ op-time op ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ [ op-time op ]ᶠ (   ⟨ op-time op ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                               ∘ᵐ ⟨ op-time op ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                               ∘ᵐ ⟨ op-time op ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ
        (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ [ op-time op ]ᶠ (⟨ op-time op ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                                ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                                ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-nat _)))) ⟩
         opᵀ op
      ∘ᵐ ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
           ∘ᵐ ⟦ V ⟧ᵛᵗ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
        (sym (∘ᵐ-assoc _ _ _))
        (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    (   ⟦⟧ᵛ-⟦⟧ᵍ (param op)
               ∘ᵐ ⟦ V ⟧ᵛᵗ)
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              (   [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
               ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
               ∘ᵐ η⊣)
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
         opᵀ op
      ∘ᵐ ⟨   ⟦⟧ᵛ-⟦⟧ᵍ (param op)
          ∘ᵐ ⟦ V ⟧ᵛᵗ
          ,
             [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
          ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
          ∘ᵐ η⊣ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   opᵀ op
          ∘ᵐ ⟨   ⟦⟧ᵛ-⟦⟧ᵍ (param op)
              ∘ᵐ ⟦ V ⟧ᵛᵗ
              ,
                 [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
              ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
              ∘ᵐ η⊣ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (handle_`with_`in {A} {B} {τ} {τ'} M H N) x W =
    begin
         uncurryᵐ (   T-alg-of-handlerᵀ
                   ∘ᵐ ⟨ (λ op →
                          ⟨ (λ τ'' →
                              (   curryᵐ (   idᵐ
                                          ∘ᵐ uncurryᵐ idᵐ
                                          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                 ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                   [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                              ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ curryᵐ (   ⟦ H op τ'' [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                   ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (uncurryᵐ-nat _ _) ⟩
         (   uncurryᵐ T-alg-of-handlerᵀ
          ∘ᵐ mapˣᵐ
               (   ⟨ (λ op →
                          ⟨ (λ τ'' →
                              (   curryᵐ (   idᵐ
                                          ∘ᵐ uncurryᵐ idᵐ
                                          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                 ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                   [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                              ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ curryᵐ (   ⟦ H op τ'' [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               idᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ (   mapˣᵐ
               (   ⟨ (λ op →
                          ⟨ (λ τ'' →
                              (   curryᵐ (   idᵐ
                                          ∘ᵐ uncurryᵐ idᵐ
                                          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                 ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                   [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                              ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ curryᵐ (   ⟦ H op τ'' [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               idᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _)))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           ((   ⟨ (λ op →
                          ⟨ (λ τ'' →
                              (   curryᵐ (   idᵐ
                                          ∘ᵐ uncurryᵐ idᵐ
                                          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                 ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                   [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                              ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ curryᵐ (   ⟦ H op τ'' [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
            ∘ᵐ idᵐ
            ∘ᵐ idᵐ)
           (idᵐ ∘ᵐ Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (∘ᵐ-identityʳ _)) (∘ᵐ-identityˡ _))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ (   ⟦ H op τ'' [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong₂ mapˣᵐ
          (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' → ∘ᵐ-congˡ (∘ᵐ-congʳ
            (cong curryᵐ (∘ᵐ-congˡ (C-subst≡∘ᵐ (H op τ'') (Tl-∷ (Tl-∷ x)) W)))))))))))
          refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ (   (   ⟦ H op τ'' ⟧ᶜᵗ
                                           ∘ᵐ mapˣᵐ (mapˣᵐ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ) idᵐ
                                           ∘ᵐ mapˣᵐ (mapˣᵐ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) idᵐ) idᵐ
                                           ∘ᵐ mapˣᵐ (mapˣᵐ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)) idᵐ) idᵐ)
                                       ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' → 
        ∘ᵐ-congˡ (∘ᵐ-congʳ (cong curryᵐ
          (sym (trans (∘ᵐ-assoc _ _ _) (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
            (trans
              (trans (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _)))) (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))
              (sym
                (trans
                  (trans (∘ᵐ-congʳ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _)))) (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))
                  (cong₂ ⟨_,_⟩ᵐ
                    (begin
                         ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
                      ∘ᵐ ⟨    (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                           ∘ᵐ fstᵐ ,
                              (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                           ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
                         ⟨    fstᵐ
                           ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                               ∘ᵐ fstᵐ ,
                                  (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                               ∘ᵐ sndᵐ ⟩ᵐ ,
                              (fstᵐ ∘ᵐ sndᵐ)
                           ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                               ∘ᵐ fstᵐ ,
                                  (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                               ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                    ≡⟨ cong₂ ⟨_,_⟩ᵐ
                        (trans (⟨⟩ᵐ-fstᵐ _ _) (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))
                        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))) ⟩
                         ⟨     split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
                            ∘ᵐ fstᵐ
                            ,
                               fstᵐ
                            ∘ᵐ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                            ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ cong₂ ⟨_,_⟩ᵐ refl
                        (trans
                          (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) (∘ᵐ-identityˡ _)))
                          (sym
                            (trans (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) (∘ᵐ-identityˡ _)))) ⟩
                         ⟨   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
                           ∘ᵐ fstᵐ
                           ,
                              (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                           ∘ᵐ fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ cong₂ ⟨_,_⟩ᵐ
                        (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))))
                        (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))) ⟩
                         ⟨    (   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                               ∘ᵐ fstᵐ)
                           ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
                           ,
                              (   (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                               ∘ᵐ sndᵐ)
                           ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
                    ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
                         mapˣᵐ
                           (  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                           (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                      ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ ∘ᵐ-congˡ (trans (mapˣᵐ-∘ᵐ _ _ _ _) (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _))) ⟩
                        (   ⟨ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                         ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                         ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
                           (   ⟨ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                            ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                            ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                         ∘ᵐ fstᵐ
                     ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                        (   (   ⟨ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                             ∘ᵐ ⟨ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                             ∘ᵐ ⟨ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                         ∘ᵐ fstᵐ)
                     ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ∎)
                    (begin
                         (sndᵐ ∘ᵐ sndᵐ)
                      ∘ᵐ ⟨    (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                           ∘ᵐ fstᵐ
                           , (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                         sndᵐ
                      ∘ᵐ sndᵐ
                      ∘ᵐ ⟨    (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                           ∘ᵐ fstᵐ
                           , (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ⟩
                         sndᵐ
                      ∘ᵐ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ
                    ≡⟨ trans
                        (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) (∘ᵐ-identityˡ _)))
                        (sym (trans (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) (∘ᵐ-identityˡ _))) ⟩
                         (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                      ∘ᵐ sndᵐ
                      ∘ᵐ sndᵐ
                    ≡⟨ sym (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) ⟩
                         (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
                      ∘ᵐ sndᵐ
                      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                         ((idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ)
                      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ∎))))))))))))))))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ (   (   ⟦ H op τ'' ⟧ᶜᵗ
                                           ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                                       ∘ᵐ mapˣᵐ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ
                                       ∘ᵐ mapˣᵐ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) idᵐ
                                       ∘ᵐ mapˣᵐ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)) idᵐ))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ
        (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op →
          ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext λ τ'' →
            ∘ᵐ-congˡ (∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congʳ
              (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                  (cong₂ mapˣᵐ refl (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))))))))))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ (   (   ⟦ H op τ'' ⟧ᶜᵗ
                                           ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                                       ∘ᵐ mapˣᵐ
                                            (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                             ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                             ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                                            idᵐ))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' →
        ∘ᵐ-congˡ (∘ᵐ-congʳ (curryᵐ-nat _ _))))))))) refl))⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' →
        ∘ᵐ-congˡ (sym (∘ᵐ-assoc _ _ _))))))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   (   curryᵐ (   idᵐ
                                           ∘ᵐ uncurryᵐ idᵐ
                                           ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                  [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                               ∘ᵐ sndᵐ ⟩ᵐ)
                                ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ∘ᵐ-congˡ (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' →
        ∘ᵐ-assoc _ _ _))))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                        ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
            ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ (
        trans
          (sym (⟨⟩ᵢᵐ-∘ᵐ _ _))
          (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ op)))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                        ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                        ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                    ∘ᵐ ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ
        (cong ⟨_⟩ᵢᵐ (fun-ext (λ op →
          trans
            (sym (⟨⟩ᵢᵐ-∘ᵐ _ _))
            (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' → trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
              (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ τ'')) (∘ᵐ-identityʳ _)))))))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                        ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)) ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ
        (trans (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → ⟨⟩ᵢᵐ-∘ᵐ _ _))) (⟨⟩ᵢᵐ-∘ᵐ _ _)) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
        (∘ᵐ-congˡ (cong  Tᶠ (C-subst≡∘ᵐ N (Tl-∷ (Tl-⟨⟩ x)) W))))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                   ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))) idᵐ
                   ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)) idᵐ
                   ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))) idᵐ)
            ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl
        (∘ᵐ-congˡ (cong Tᶠ (∘ᵐ-congʳ (
          trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _)))))))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                   ∘ᵐ mapˣᵐ
                        (   ⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                         ∘ᵐ ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                         ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                        (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ))
            ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (∘ᵐ-congˡ (cong Tᶠ (∘ᵐ-congʳ
        (cong₂ mapˣᵐ
          (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))
          (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))))))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (   Tᶠ (   ⟦ N ⟧ᶜᵗ
                   ∘ᵐ mapˣᵐ
                        (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                 ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                        idᵐ)
            ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (trans (∘ᵐ-congˡ (T-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (   Tᶠ ⟦ N ⟧ᶜᵗ
            ∘ᵐ (   Tᶠ (mapˣᵐ
                       (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                       idᵐ)
                ∘ᵐ strᵀ))
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ refl (∘ᵐ-congʳ (sym (strᵀ-nat _ _))))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (   ⟨ (λ op →
                       ⟨ (λ τ'' →
                           (   curryᵐ (   idᵐ
                                       ∘ᵐ uncurryᵐ idᵐ
                                       ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                            ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                              [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                           ∘ᵐ sndᵐ ⟩ᵐ)
                            ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (   Tᶠ ⟦ N ⟧ᶜᵗ
            ∘ᵐ strᵀ
            ∘ᵐ mapˣᵐ
                  ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                  (Tᶠ idᵐ))
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
        (cong₂ mapˣᵐ refl (∘ᵐ-assoc _ _ _))))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ (   mapˣᵐ
              (   ⟨ (λ op →
                          ⟨ (λ τ'' →
                              (   curryᵐ (   idᵐ
                                          ∘ᵐ uncurryᵐ idᵐ
                                          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                               ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                 [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                              ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ)
              (   Tᶠ ⟦ N ⟧ᶜᵗ
               ∘ᵐ strᵀ)
          ∘ᵐ mapˣᵐ
              (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
              (mapˣᵐ
                  ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                  (Tᶠ idᵐ)))
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
          (   ⟨ (λ op →
                      ⟨ (λ τ'' →
                          (   curryᵐ (   idᵐ
                                      ∘ᵐ uncurryᵐ idᵐ
                                      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                           ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                             [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                          ∘ᵐ sndᵐ ⟩ᵐ)
                           ∘ᵐ curryᵐ ( ⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ) ⟩ᵢᵐ) ⟩ᵢᵐ)
          (   Tᶠ ⟦ N ⟧ᶜᵗ
           ∘ᵐ strᵀ)
      ∘ᵐ mapˣᵐ
          (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          (mapˣᵐ
              ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
              (Tᶠ idᵐ))
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (
        begin
             mapˣᵐ
              (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
              (mapˣᵐ
                  ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                  (Tᶠ idᵐ))
          ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
             ⟨       ((   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                       ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
                  ∘ᵐ fstᵐ)
               ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
             ,       ((mapˣᵐ
                        ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                         ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                         ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                        (Tᶠ idᵐ))
                  ∘ᵐ sndᵐ)
               ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))) refl ⟩
             ⟨    (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
               ∘ᵐ idᵐ
             ,       ((mapˣᵐ
                        ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                         ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                         ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                        (Tᶠ idᵐ))
                  ∘ᵐ sndᵐ)
               ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ refl (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))) ⟩
             ⟨    (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
               ∘ᵐ idᵐ
             ,    (mapˣᵐ
                     ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                     (Tᶠ idᵐ))
               ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityʳ _) (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
             ⟨   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
             ,    ⟨    (  ([ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
                       ∘ᵐ fstᵐ)
                    ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ
                  ,    (  (Tᶠ idᵐ)
                       ∘ᵐ sndᵐ)
                    ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ refl
            (cong₂ ⟨_,_⟩ᵐ
              (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
              (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))) ⟩
             ⟨   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
             ,    ⟨    [ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                       ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                    ∘ᵐ η⊣
                  ,    (Tᶠ idᵐ)
                    ∘ᵐ ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ
            (sym (∘ᵐ-identityˡ _))
            (cong₂ ⟨_,_⟩ᵐ refl
              (trans (∘ᵐ-congˡ T-idᵐ) (∘ᵐ-identityˡ _))) ⟩
             ⟨    idᵐ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
               ,
                  ⟨    [ τ ]ᶠ (⟨ τ ⟩ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                                       ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
                    ∘ᵐ η⊣
                    , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ
            (η⊣-nat _)
            (C-subst≡∘ᵐ M x W)) ⟩
             ⟨    idᵐ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
               ,
                  ⟨    η⊣
                    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 
                    ,
                       ⟦ M ⟧ᶜᵗ
                    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ refl (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
             ⟨    idᵐ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
               ,
                  ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
        ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
             ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ∎)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           ( ⟨ (λ op →
                       ⟨ (λ τ'' →
                              (  curryᵐ (   idᵐ
                                         ∘ᵐ uncurryᵐ idᵐ
                                         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                              ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ
        (sym (trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _)) (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → trans (∘ᵐ-assoc _ _ _)
          (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ op)) (trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _))
            (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' → trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ τ'')) (∘ᵐ-identityʳ _)))))))))))) refl)) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           ( ⟨ (λ op →
                       ⟨ (λ τ'' →
                              (  curryᵐ (   idᵐ
                                         ∘ᵐ uncurryᵐ idᵐ
                                         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                              ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                        ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
           (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ mapˣᵐ
        (sym (trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (∘ᵐ-identityʳ _)))
        (sym (∘ᵐ-identityˡ _)))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ mapˣᵐ
           (( ⟨ (λ op →
                       ⟨ (λ τ'' →
                              (  curryᵐ (   idᵐ
                                         ∘ᵐ uncurryᵐ idᵐ
                                         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                              ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                        ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
            ∘ᵐ idᵐ
            ∘ᵐ idᵐ)
           (idᵐ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (trans (mapˣᵐ-∘ᵐ _ _ _ _) (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _)))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ (   mapˣᵐ
               ( ⟨ (λ op →
                       ⟨ (λ τ'' →
                              (  curryᵐ (   idᵐ
                                         ∘ᵐ uncurryᵐ idᵐ
                                         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                              ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                        ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               idᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ ∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (sym (trans
        (∘ᵐ-congˡ (sym (∘ᵐ-assoc _ _ _))) (∘ᵐ-assoc _ _ _)))) (sym (∘ᵐ-assoc _ _ _)))) ⟩
         uncurryᵐ T-alg-of-handlerᵀ
      ∘ᵐ (   mapˣᵐ
               ( ⟨ (λ op →
                       ⟨ (λ τ'' →
                              (  curryᵐ (   idᵐ
                                         ∘ᵐ uncurryᵐ idᵐ
                                         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                              ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                        ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               idᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   uncurryᵐ T-alg-of-handlerᵀ
          ∘ᵐ mapˣᵐ
               ( ⟨ (λ op →
                       ⟨ (λ τ'' →
                              (  curryᵐ (   idᵐ
                                         ∘ᵐ uncurryᵐ idᵐ
                                         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                              ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                         ∘ᵐ sndᵐ ⟩ᵐ)
                              ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                        ∘ᵐ projᵐ op) ⟩ᵢᵐ
                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
               idᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-assoc _ _ _)) ⟩
         (   (   uncurryᵐ T-alg-of-handlerᵀ
              ∘ᵐ mapˣᵐ
                   ( ⟨ (λ op →
                           ⟨ (λ τ'' →
                                  (  curryᵐ (   idᵐ
                                             ∘ᵐ uncurryᵐ idᵐ
                                             ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                  ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                    [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                             ∘ᵐ sndᵐ ⟩ᵐ)
                                  ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                               ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                            ∘ᵐ projᵐ op) ⟩ᵢᵐ
                    ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                   idᵐ)
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _))) ⟩
         (  uncurryᵐ (   T-alg-of-handlerᵀ
                      ∘ᵐ ⟨ (λ op →
                             ⟨ (λ τ'' →
                                    (  curryᵐ (   idᵐ
                                               ∘ᵐ uncurryᵐ idᵐ
                                               ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                    ⟨ ⟦⟧ᵍ-⟦⟧ᵛ (param op) ∘ᵐ fstᵐ ,
                                                      [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ sndᵐ ⟩ᵐ
                                               ∘ᵐ sndᵐ ⟩ᵐ)
                                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                                 ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                              ∘ᵐ projᵐ op) ⟩ᵢᵐ
                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
         ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
         ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ {τ = τ} (unbox {τ = τ'} p V M) x W with τ' ≤? τ
  C-subst≡∘ᵐ {Γ = Γ} {τ = τ} (unbox {A = A} {τ = τ'} p V M) x W | yes q with var-in-ctx-after-ᶜ x q
  ... | y , r , s =
    begin
         ⟦ M [ Tl-∷ x ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename
                          (   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s))
                          (V [ y ↦ V-rename (eq-ren (sym r)) W ]v) ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (C-subst≡∘ᵐ M (Tl-∷ x) W) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename
                          (   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s))
                          (V [ y ↦ V-rename (eq-ren (sym r)) W ]v) ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename
                          (   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s))
                          (V [ y ↦ V-rename (eq-ren (sym r)) W ]v) ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ
        (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ' ⟩ᶠ (V-rename≡∘ᵐ (
                                            (   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                                             ∘ʳ eq-ren (cong₂ _++ᶜ_ r s)))
                                            (V [ y ↦ V-rename (eq-ren (sym r)) W ]v))))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V [ y ↦ V-rename (eq-ren (sym r)) W ]v ⟧ᵛᵗ
                       ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ
        (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ' ⟩ᶠ (∘ᵐ-congˡ (V-subst≡∘ᵐ V y (V-rename (eq-ren (sym r)) W)))))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ (   (   ⟦ V ⟧ᵛᵗ
                           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl) )
                       ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong ⟨ τ' ⟩ᶠ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                       ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                       ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                       ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ mapˣᵐ
           (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                       ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                       ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                       ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                           ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (  (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                 ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
             ∘ᵐ fstᵐ)
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                           ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                               ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
          ,
             ((idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ)
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                           ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                               ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          ∘ᵐ fstᵐ
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                           ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                               ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
          ,
             (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
          ∘ᵐ sndᵐ
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                           ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                           ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                           ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                               ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          ∘ᵐ idᵐ
          ,
             (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
          ∘ᵐ ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                      ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                      ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                      ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                          ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          ∘ᵐ idᵐ
          ,
             idᵐ
          ∘ᵐ ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                      ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                      ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                      ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                          ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
              ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
              ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          ,
             ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                      ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                      ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                      ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                          ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (sym (∘ᵐ-identityˡ _)) (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   idᵐ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             ε⊣
          ∘ᵐ (   ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
              ∘ᵐ ⟨ τ' ⟩ᶠ (  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                          ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                          ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                          ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                              ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ))
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   idᵐ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
          ∘ᵐ ⟨ τ' ⟩ᶠ (  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                      ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                      ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                      ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                          ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congʳ (
        begin
             ⟨ τ' ⟩ᶠ (  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                      ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                      ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                      ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                          ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
        ≡⟨ C-subst≡∘ᵐ-aux-unbox x y W p q r s ⟩
             env-⟨⟩-ᶜ τ' p
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ∎)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨    idᵐ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' p
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨    idᵐ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
              (   ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ' p)
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ' p ⟩ᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵐ ⟨ idᵐ ,
               ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ' p ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ {A = B} {τ = τ} (unbox {A = A} {τ = τ'} p V M) x W | no ¬q =
    begin
         ⟦ M [ Tl-∷ x ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (C-subst≡∘ᵐ M (Tl-∷ x) W) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-∷ {B = A} x)))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-∷ {B = A} x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env
               {Γ' = proj₁ (var-split (Tl-∷ {B = A} x))}
               {Γ'' = proj₁ (proj₂ (var-split (Tl-∷ {B = A} x)))}
               (split-∷ (≡-split refl)))
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (sym (mapˣᵐ-∘ᵐ _ _ _ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ mapˣᵐ
           (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
           (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨  (   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                 ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
             ∘ᵐ fstᵐ)
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
          ,
             ((idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ)
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          ∘ᵐ fstᵐ
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
          ,
             (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
          ∘ᵐ sndᵐ
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨   (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
          ∘ᵐ idᵐ
          ,
             (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
          ∘ᵐ ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (∘ᵐ-identityʳ _) (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             idᵐ
          ∘ᵐ ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-identityˡ _)) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V ⟧ᵛᵗ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ' ⟩ᶠ (V-rename≡∘ᵐ (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q))) V))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ V ⟧ᵛᵗ
                      ∘ᵐ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ,
             ε⊣
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (∘ᵐ-congʳ (
        begin
             ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
        ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _)) ⟩
             ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
          ∘ᵐ idᵐ
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (split-env-wk-ren {proj₁ (var-split x)} {proj₁ (proj₂ (var-split x))} ⟦ W ⟧ᵛᵗ))) ⟩
             ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
          ∘ᵐ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren ⟧ʳ
          ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ B} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
            (env-⟨⟩-ᶜ-ren-nat _ _ (cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren))) (∘ᵐ-assoc _ _ _))) ⟩
             ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren -ʳ τ' ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ'
              (≤-trans
               (≤-trans p
                (≤-reflexive
                 (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
               (ren-≤-ctx-time (cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren)))
          ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ B} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong (env-⟨⟩-ᶜ τ') (≤-irrelevant _ _)))) ⟩
             ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
          ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren -ʳ τ' ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (cong ctx-time (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
          ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ B} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
             (   ⟨ τ' ⟩ᶠ ⟦ eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬q)) ⟧ʳ
              ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren -ʳ τ' ⟧ʳ)
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (cong ctx-time (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
          ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ B} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ≡⟨ ∘ᵐ-congˡ (trans (sym (⟨⟩-∘ᵐ _ _)) (cong ⟨ τ' ⟩ᶠ (var-not-in-ctx-after-ᶜ-wk-ren (≰⇒> ¬q) x))) ⟩
             ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
          ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (cong ctx-time (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
          ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ B} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (env-⟨⟩-ᶜ-eq-ren-nat _ _ _))) (∘ᵐ-assoc _ _ _)) ⟩
             env-⟨⟩-ᶜ τ' p
          ∘ᵐ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))) ⟧ʳ
          ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ B} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (sym (split-env⁻¹-eq-ren (proj₁ (proj₂ (proj₂ (var-split x)))))))) ⟩
             env-⟨⟩-ᶜ τ' p
          ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
          ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
          ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
        ∎)))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨    split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              ε⊣
           ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ' p
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
        (sym (∘ᵐ-identityˡ _))
        (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨    idᵐ
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
           ,
              (ε⊣ ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ' p)
           ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
           ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
           ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨ idᵐ ,
           ε⊣ ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ' p ⟩ᵐ 
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵐ ⟨ idᵐ ,
               ε⊣ ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ' p ⟩ᵐ)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  C-subst≡∘ᵐ (delay τ M) x W =
    begin
         delayᵀ τ
      ∘ᵐ [ τ ]ᶠ ⟦ M [ Tl-⟨⟩ x ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τ ]ᶠ (C-subst≡∘ᵐ M (Tl-⟨⟩ x) W))) ⟩
         delayᵀ τ
      ∘ᵐ [ τ ]ᶠ (   ⟦ M ⟧ᶜᵗ
                 ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-⟨⟩ x)))))
                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-⟨⟩ x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                 ∘ᵐ split-env
                      {Γ' = proj₁ (var-split (Tl-⟨⟩ {τ = τ} x))}
                      {Γ'' = proj₁ (proj₂ (var-split (Tl-⟨⟩ x)))}
                      (split-⟨⟩ (≡-split refl)))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)) ⟩
         delayᵀ τ
      ∘ᵐ (   [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
          ∘ᵐ [ τ ]ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-⟨⟩ x)))))
                     ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-⟨⟩ x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                     ∘ᵐ split-env
                          {Γ' = proj₁ (var-split (Tl-⟨⟩ {τ = τ} x))}
                          {Γ'' = proj₁ (proj₂ (var-split (Tl-⟨⟩ x)))}
                          (split-⟨⟩ (≡-split refl))))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
         delayᵀ τ
      ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
      ∘ᵐ [ τ ]ᶠ (   split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split (Tl-⟨⟩ x)))))
                 ∘ᵐ ⟦ proj₁ (proj₂ (var-split (Tl-⟨⟩ x))) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                 ∘ᵐ split-env
                      {Γ' = proj₁ (var-split (Tl-⟨⟩ {τ = τ} x))}
                      {Γ'' = proj₁ (proj₂ (var-split (Tl-⟨⟩ x)))}
                      (split-⟨⟩ (≡-split refl)))
      ∘ᵐ η⊣
    ≡⟨⟩
         delayᵀ τ
      ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
      ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))) ∘ᵐ
                 ⟨ τ ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ
                 ⟨ τ ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong [ τ ]ᶠ (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))))) ⟩
         delayᵀ τ
      ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
      ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ (   (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x)))))
                         ∘ᵐ (⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
                         ∘ᵐ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))))
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-nat _)) ⟩
         delayᵀ τ
      ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
      ∘ᵐ η⊣
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
         (   delayᵀ τ
          ∘ᵐ [ τ ]ᶠ ⟦ M ⟧ᶜᵗ
          ∘ᵐ η⊣)
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎


