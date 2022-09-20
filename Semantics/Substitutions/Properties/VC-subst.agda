-----------------------------------------------------------------------
-- Relating syntactic substitutions to semantic morphism composition --
-----------------------------------------------------------------------

open import Semantics.Model

module Semantics.Substitutions.Properties.VC-subst (Mod : Model) where

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Substitutions

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Semantics.Interpretation.Properties.split-env-isomorphism Mod
open import Semantics.Interpretation.Properties.split-env-naturality Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

mutual

  V-subst : ∀ {Γ A B τ}
          → (V : Γ ⊢V⦂ B)
          → (x : A ∈[ τ ] Γ)
          → (W : proj₁ (var-split x) ⊢V⦂ A)
          → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
          ≡    ⟦ V ⟧ᵛᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  V-subst (var y) x W = {!!}
  V-subst (const c) x W = 
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
  V-subst ⋆ x W = 
    begin
      terminalᵐ
    ≡⟨ sym terminalᵐ-unique ⟩
         terminalᵐ
      ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
      ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
      ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∎
  V-subst (lam {A = A} M) x W = 
    begin
      curryᵐ ⟦ M [ Tl-∷ x ↦ W ]c ⟧ᶜᵗ
    ≡⟨ cong curryᵐ (C-subst M (Tl-∷ x) W) ⟩
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
  V-subst {A = A} (box {B} {τ} V) x W = 
    begin
         [ τ ]ᶠ ⟦ V [ Tl-⟨⟩ x ↦ W ]v ⟧ᵛᵗ
      ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (V-subst V (Tl-⟨⟩ x) W)) ⟩
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


  C-subst : ∀ {Γ A C τ}
          → (M : Γ ⊢C⦂ C)
          → (x : A ∈[ τ ] Γ)
          → (W : proj₁ (var-split x) ⊢V⦂ A)
          → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ
          ≡    ⟦ M ⟧ᶜᵗ
            ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
            ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
            ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) 

  C-subst (return V) x W = 
    begin
         ηᵀ
      ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-subst V x W) ⟩
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
  C-subst (_;_ {A = A} {τ = τ} M N) x W = 
    begin
         μᵀ
      ∘ᵐ Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ η⊣ ,_⟩ᵐ (C-subst M x W)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ ,   ⟦ M ⟧ᶜᵗ
               ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
               ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
               ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (C-subst N (Tl-∷ (Tl-⟨⟩ x)) W))) ⟩
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
  C-subst (V · V') x W = {!!}
  C-subst (absurd V) x W = 
    begin
         initialᵐ
      ∘ᵐ ⟦ V [ x ↦ W ]v ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-subst V x W) ⟩
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
  C-subst (perform op V M) x W = {!!}
  C-subst (handle M `with H `in M₁) x W = {!!}
  C-subst (unbox p V M) x W = {!!}
  C-subst (delay τ M) x W = {!!}
