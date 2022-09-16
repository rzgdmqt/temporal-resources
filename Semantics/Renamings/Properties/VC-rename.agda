----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.VC-rename (Mod : Model) where

open import Data.Product

open import Syntax.Types
open import Syntax.Language
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-naturality Mod
open import Semantics.Renamings.Properties.var-in-env-var-rename Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

mutual

  V-rename≡∘ᵗ : ∀ {Γ Γ' A}
              → (ρ : Ren Γ Γ')
              → (V : Γ ⊢V⦂ A)
              → ⟦ V-rename ρ V ⟧ᵛᵗ
             ≡ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ

  V-rename≡∘ᵗ {Γ} {Γ'} {A} ρ (var {τ = τ} x) =
    begin
      var-in-env (proj₂ (proj₂ (var-rename ρ x)))
    ≡⟨ var-in-env∘var-rename≡var-rename∘ᵗ⟦⟧ʳ ρ x ⟩
      var-in-env x ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵗ ρ (const c) =
    begin
      constᵗ c ∘ᵗ terminalᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym terminalᵗ-unique) ⟩
      constᵗ c ∘ᵗ (terminalᵗ ∘ᵗ ⟦ ρ ⟧ʳ)
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      (constᵗ c ∘ᵗ terminalᵗ) ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵗ ρ ⋆ =
    begin
      terminalᵗ
    ≡⟨ ≡ᵗ-sym terminalᵗ-unique ⟩
      terminalᵗ ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵗ ρ (lam {A} M) =
    begin
      curryᵗ ⟦ C-rename (cong-∷-ren ρ) M ⟧ᶜᵗ
    ≡⟨ ≡ᵗ-cong curryᵗ (C-rename≡∘ᵗ (cong-∷-ren ρ) M) ⟩
      curryᵗ (⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ cong-∷-ren {A = A} ρ ⟧ʳ)
    ≡⟨⟩
      curryᵗ (⟦ M ⟧ᶜᵗ ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ)
    ≡⟨ curryᵗ-mapˣᵗ ⟦ M ⟧ᶜᵗ ⟦ ρ ⟧ʳ idᵗ ⟩
      map⇒ᵗ idᵗ idᵗ ∘ᵗ curryᵗ ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵗ-congˡ map⇒ᵗ-identity ⟩
      idᵗ ∘ᵗ curryᵗ ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵗ-identityˡ _ ⟩
      curryᵗ ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵗ ρ (box {τ = τ} V) =
    begin
      [ τ ]ᶠ ⟦ V-rename (cong-⟨⟩-ren ρ) V ⟧ᵛᵗ ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong [ τ ]ᶠ (V-rename≡∘ᵗ (cong-⟨⟩-ren ρ) V)) ⟩
      [ τ ]ᶠ (⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ cong-⟨⟩-ren ρ ⟧ʳ) ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-congˡ ([]-∘ᵗ ⟦ cong-⟨⟩-ren ρ ⟧ʳ ⟦ V ⟧ᵛᵗ) ⟩
      ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ [ τ ]ᶠ ⟦ cong-⟨⟩-ren ρ ⟧ʳ) ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ ([ τ ]ᶠ ⟦ cong-⟨⟩-ren ρ ⟧ʳ ∘ᵗ η⊣)
    ≡⟨⟩
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-congʳ (η⊣-nat _) ⟩
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ η⊣ ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ η⊣) ∘ᵗ ⟦ ρ ⟧ʳ
    ∎

  C-rename≡∘ᵗ : ∀ {Γ Γ' C}
              → (ρ : Ren Γ Γ')
              → (M : Γ ⊢C⦂ C)
              → ⟦ C-rename ρ M ⟧ᶜᵗ
             ≡ᵗ ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ

  C-rename≡∘ᵗ ρ (return V) = 
    begin
      ηᵀ ∘ᵗ ⟦ V-rename ρ V ⟧ᵛᵗ
    ≡⟨ ∘ᵗ-congʳ (V-rename≡∘ᵗ ρ V) ⟩
      ηᵀ ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      (ηᵀ ∘ᵗ ⟦ V ⟧ᵛᵗ) ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ {Γ} {Γ'} ρ (_;_ {A} {B} {τ} {τ'} M N) =
    begin
         μᵀ
      ∘ᵗ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) N ⟧ᶜᵗ
      ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵗ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ C-rename ρ M ⟧ᶜᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-cong ⟨ η⊣ ,_⟩ᵗ (C-rename≡∘ᵗ ρ M)))) ⟩
         μᵀ
      ∘ᵗ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) N ⟧ᶜᵗ
      ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵗ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-cong Tᶠ (C-rename≡∘ᵗ (cong-∷-ren (cong-⟨⟩-ren ρ)) N))) ⟩
         μᵀ
      ∘ᵗ Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ ⟦ cong-∷-ren {A = A} (cong-⟨⟩-ren ρ) ⟧ʳ)
      ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵗ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (Tᶠ-∘ᵗ _ _)) ⟩
         μᵀ
      ∘ᵗ (   Tᶠ (⟦ N ⟧ᶜᵗ)
          ∘ᵗ Tᶠ ⟦ cong-∷-ren {A = A} (cong-⟨⟩-ren ρ) ⟧ʳ)
      ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵗ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-assoc _ _ _) ⟩
         μᵀ
      ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵗ Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ)
      ∘ᵗ strᵀ
      ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (
           begin
                Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ)
             ∘ᵗ strᵀ
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
                (   Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ)
                 ∘ᵗ strᵀ)
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (strᵀ-nat _ _)) ⟩
                (   strᵀ
                 ∘ᵗ mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) (Tᶠ idᵗ))
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
                strᵀ
             ∘ᵗ mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) (Tᶠ idᵗ)
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-cong (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ))) Tᶠ-idᵗ)) ⟩
                strᵀ
             ∘ᵗ mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨⟩
                strᵀ
             ∘ᵗ ⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵗ fstᵗ , idᵗ ∘ᵗ sndᵗ ⟩ᵗ
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (⟨⟩ᵗ-∘ᵗ _ _ _)) ⟩
                strᵀ
             ∘ᵗ ⟨ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵗ fstᵗ) ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ,
                  (idᵗ ∘ᵗ sndᵗ) ∘ᵗ ⟨ η⊣ {τ = τ} , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
           ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong₂ ⟨_,_⟩ᵗ
               (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _)))
               (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (≡ᵗ-trans (∘ᵗ-identityˡ _) (⟨⟩ᵗ-sndᵗ _ _)))) ⟩
                strᵀ
             ∘ᵗ ⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵗ η⊣ ,
                  ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong ⟨_, ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ (η⊣-nat _)) ⟩
                strᵀ
             ∘ᵗ ⟨ η⊣ ∘ᵗ ⟦ ρ ⟧ʳ ,
                  ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
           ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-∘ᵗ _ _ _) ⟩
                strᵀ
             ∘ᵗ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵗ
             ∘ᵗ ⟦ ρ ⟧ʳ
           ∎)) ⟩
         μᵀ
      ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵗ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ
      ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _))) ⟩
         μᵀ
      ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵗ (   strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
          ∘ᵗ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ)
      ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
         μᵀ
      ∘ᵗ (Tᶠ ⟦ N ⟧ᶜᵗ
          ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
          ∘ᵗ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ)
      ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
         (   μᵀ
          ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
          ∘ᵗ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
          ∘ᵗ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ)
      ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ ρ (V · W) = 
    begin
      appᵗ ∘ᵗ ⟨ ⟦ V-rename ρ V ⟧ᵛᵗ , ⟦ V-rename ρ W ⟧ᵛᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong₂ ⟨_,_⟩ᵗ (V-rename≡∘ᵗ ρ V) (V-rename≡∘ᵗ ρ W))
     ⟩
      appᵗ ∘ᵗ ⟨ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ , ⟦ W ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-∘ᵗ _ _ _) ⟩
      appᵗ ∘ᵗ (⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵗ ∘ᵗ ⟦ ρ ⟧ʳ)
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      (appᵗ ∘ᵗ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵗ) ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ ρ (absurd V) =
    begin
      initialᵗ ∘ᵗ ⟦ V-rename ρ V ⟧ᵛᵗ
    ≡⟨ ∘ᵗ-congʳ (V-rename≡∘ᵗ ρ V) ⟩
      initialᵗ ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      (initialᵗ ∘ᵗ ⟦ V ⟧ᵛᵗ) ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ ρ (perform op V M) =
    begin
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V-rename ρ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) M ⟧ᶜᵗ)
           ∘ᵗ η⊣ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong₂ ⟨_,_⟩ᵗ
        (∘ᵗ-congʳ (V-rename≡∘ᵗ ρ V))
        (∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-cong
                              (λ f → [ op-time op ]ᶠ (curryᵗ f))
                              (C-rename≡∘ᵗ (cong-∷-ren (cong-⟨⟩-ren ρ)) M))))) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ
                (curryᵗ (   ⟦ M ⟧ᶜᵗ
                         ∘ᵗ ⟦ (cong-∷-ren {A = type-of-gtype (arity op)} (cong-⟨⟩-ren ρ)) ⟧ʳ) )
           ∘ᵗ η⊣ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,_⟩ᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
        (≡ᵗ-cong [ op-time op ]ᶠ (curryᵗ-mapˣᵗ _ _ _))))) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (map⇒ᵗ idᵗ idᵗ ∘ᵗ curryᵗ ⟦ M ⟧ᶜᵗ ∘ᵗ ⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ)
           ∘ᵗ η⊣ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,_⟩ᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
        (≡ᵗ-cong [ op-time op ]ᶠ (≡ᵗ-trans (∘ᵗ-congˡ map⇒ᵗ-identity) (∘ᵗ-identityˡ _)))))) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ ∘ᵗ ⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ)
           ∘ᵗ η⊣ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,_⟩ᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
        ([]-∘ᵗ (⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ) (curryᵗ ⟦ M ⟧ᶜᵗ))))) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ (   [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
               ∘ᵗ [ op-time op ]ᶠ(⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ))
           ∘ᵗ η⊣ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,_⟩ᵗ (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _))) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
           ∘ᵗ (   [ op-time op ]ᶠ(⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ)
               ∘ᵗ η⊣) ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,_⟩ᵗ (∘ᵗ-congʳ (∘ᵗ-congʳ (η⊣-nat _)))) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
           ∘ᵗ (   η⊣ 
               ∘ᵗ ⟦ ρ ⟧ʳ) ⟩ᵗ
    ≡⟨⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
           ∘ᵗ η⊣ 
           ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong₂ ⟨_,_⟩ᵗ
                  (≡ᵗ-sym (∘ᵗ-assoc _ _ _))
                  (≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-assoc _ _ _) (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _))))) ⟩
         opᵀ op
      ∘ᵗ ⟨    (   ⟦⟧ᵛ-⟦⟧ᵍ (param op)
               ∘ᵗ ⟦ V ⟧ᵛᵗ)
           ∘ᵗ ⟦ ρ ⟧ʳ ,
              (   [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
               ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
               ∘ᵗ η⊣)
           ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (⟨⟩ᵗ-∘ᵗ _ _ _) ⟩
         opᵀ op
      ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
           ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
           ∘ᵗ η⊣ ⟩ᵗ
      ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      (   opᵀ op
       ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ,
               [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵗ)
            ∘ᵗ [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ)
            ∘ᵗ η⊣ ⟩ᵗ)
      ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ {Γ} {Γ'} ρ (handle_`with_`in {A} {B} {τ} {τ'} M H N) =
    begin
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                 (λ τ'' →
                    map⇒ᵗ
                    (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                     ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                    idᵗ
                    ∘ᵗ
                    curryᵗ
                    (   ⟦ C-rename (cong-∷-ren (cong-∷-ren ρ)) (H op τ'') ⟧ᶜᵗ
                     ∘ᵗ ×ᵗ-assoc)))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) N ⟧ᶜᵗ)
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ C-rename ρ M ⟧ᶜᵗ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong₂ _∘ᵗ_
         (≡ᵗ-cong (mapˣᵗ idᵗ) (≡ᵗ-cong Tᶠ (C-rename≡∘ᵗ ((cong-∷-ren (cong-⟨⟩-ren ρ))) N)))
         (∘ᵗ-congʳ (≡ᵗ-cong ⟨ idᵗ ,_⟩ᵗ (≡ᵗ-cong ⟨ η⊣ ,_⟩ᵗ (C-rename≡∘ᵗ ρ M))))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                 (λ τ'' →
                    map⇒ᵗ
                    (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                     ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                    idᵗ
                    ∘ᵗ
                    curryᵗ
                    (   ⟦ C-rename (cong-∷-ren (cong-∷-ren ρ)) (H op τ'') ⟧ᶜᵗ
                     ∘ᵗ ×ᵗ-assoc)))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
         (≡-≡ᵗ (cong mapⁱˣᵗ (fun-ext (λ op → cong mapⁱˣᵗ (fun-ext (λ τ'' →
           (≡ᵗ-≡
             (∘ᵗ-congʳ (≡ᵗ-cong curryᵗ (∘ᵗ-congˡ
                (C-rename≡∘ᵗ (cong-∷-ren (cong-∷-ren ρ)) (H op τ''))))))))))))))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                   (λ τ'' →
                     map⇒ᵗ
                     (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                      ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                     idᵗ
                     ∘ᵗ
                     curryᵗ
                     (   (   ⟦ H op τ'' ⟧ᶜᵗ
                          ∘ᵗ ⟦ (cong-∷-ren {A = [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')}
                                 (cong-∷-ren {A = type-of-gtype (param op)} ρ)) ⟧ʳ)
                      ∘ᵗ ×ᵗ-assoc)))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                   (λ τ'' →
                        map⇒ᵗ
                          (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                          idᵗ
                     ∘ᵗ curryᵗ
                          (   (   ⟦ H op τ'' ⟧ᶜᵗ
                               ∘ᵗ mapˣᵗ (mapˣᵗ ⟦ ρ ⟧ʳ idᵗ) idᵗ)
                           ∘ᵗ ×ᵗ-assoc)))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
        (≡-≡ᵗ (cong mapⁱˣᵗ (fun-ext (λ op → cong mapⁱˣᵗ (fun-ext (λ τ'' →
          ≡ᵗ-≡ (∘ᵗ-congʳ (
            begin
              curryᵗ ((⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ mapˣᵗ (mapˣᵗ ⟦ ρ ⟧ʳ idᵗ) idᵗ) ∘ᵗ ×ᵗ-assoc)
            ≡⟨ ≡ᵗ-cong curryᵗ (∘ᵗ-assoc _ _ _) ⟩
              curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ (mapˣᵗ (mapˣᵗ ⟦ ρ ⟧ʳ idᵗ) idᵗ ∘ᵗ ×ᵗ-assoc))
            ≡⟨ ≡ᵗ-cong curryᵗ (∘ᵗ-congʳ (mapˣᵗ-×ᵗ-assoc _ _ _)) ⟩
              curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ (×ᵗ-assoc ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ idᵗ idᵗ)))
            ≡⟨ ≡ᵗ-cong curryᵗ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
              curryᵗ ((⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc) ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ idᵗ idᵗ))
            ≡⟨ curryᵗ-mapˣᵗ _ _ _ ⟩
              map⇒ᵗ (mapˣᵗ idᵗ idᵗ) idᵗ ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc) ∘ᵗ ⟦ ρ ⟧ʳ
            ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong (λ f → map⇒ᵗ f idᵗ) (≡ᵗ-sym
                 (⟨⟩ᵗ-unique _ _ _
                   (≡ᵗ-trans (∘ᵗ-identityʳ _) (≡ᵗ-sym (∘ᵗ-identityˡ _)))
                   (≡ᵗ-trans (∘ᵗ-identityʳ _) (≡ᵗ-sym (∘ᵗ-identityˡ _)))))) ⟩
              map⇒ᵗ idᵗ idᵗ ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc) ∘ᵗ ⟦ ρ ⟧ʳ
            ≡⟨ ∘ᵗ-congˡ map⇒ᵗ-identity ⟩
              idᵗ ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc) ∘ᵗ ⟦ ρ ⟧ʳ
            ≡⟨ ∘ᵗ-identityˡ _ ⟩
              curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc) ∘ᵗ ⟦ ρ ⟧ʳ
            ∎))))))))))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                   (λ τ'' →
                        map⇒ᵗ
                          (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                          idᵗ
                     ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)
                     ∘ᵗ ⟦ ρ ⟧ʳ))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
         (≡-≡ᵗ (cong mapⁱˣᵗ (fun-ext (λ op → cong mapⁱˣᵗ (fun-ext (λ τ'' →
            ≡ᵗ-≡ (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))))))))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                   (λ τ'' →
                        (   map⇒ᵗ
                             (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                               ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                             idᵗ
                         ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))
                     ∘ᵗ ⟦ ρ ⟧ʳ))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
         (≡-≡ᵗ (cong mapⁱˣᵗ (fun-ext (λ op →
           ≡ᵗ-≡ (mapⁱˣᵗ-∘ᵗ _ _)))))))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ (  mapⁱˣᵗ
                (λ op →
                   mapⁱˣᵗ
                     (λ τ'' →
                          map⇒ᵗ
                            (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                              ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                            idᵗ
                       ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))
                       ∘ᵗ mapⁱˣᵗ (λ τ'' → ⟦ ρ ⟧ʳ)))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-congˡ
         (mapⁱˣᵗ-∘ᵗ _ _)))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ ((  mapⁱˣᵗ
                (λ op →
                   mapⁱˣᵗ
                     (λ τ'' →
                          map⇒ᵗ
                            (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                              ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                            idᵗ
                       ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
            ∘ᵗ mapⁱˣᵗ (λ op → mapⁱˣᵗ (λ τ'' → ⟦ ρ ⟧ʳ)))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ (mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                   (λ τ'' →
                        map⇒ᵗ
                          (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                          idᵗ
                     ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
         ∘ᵗ mapⁱˣᵗ (λ op → mapⁱˣᵗ (λ τ'' → ⟦ ρ ⟧ʳ))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-congʳ (∘ᵗ-congʳ
         (≡ᵗ-trans
           (≡ᵗ-sym (⟨⟩ᵢᵗ-∘ᵗ _ _))
           (≡-≡ᵗ (cong ⟨_⟩ᵢᵗ (fun-ext λ op →
             ≡ᵗ-≡
               (≡ᵗ-trans
                 (∘ᵗ-assoc _ _ _)
                   (≡ᵗ-trans
                     (∘ᵗ-congʳ (⟨⟩ᵢᵗ-projᵗ _ op))
                     (≡ᵗ-trans
                       (≡ᵗ-sym (⟨⟩ᵢᵗ-∘ᵗ _ _))
                       (≡-≡ᵗ (cong ⟨_⟩ᵢᵗ (fun-ext (λ τ'' →
                         ≡ᵗ-≡
                           (≡ᵗ-trans
                             (∘ᵗ-assoc _ _ _)
                             (≡ᵗ-trans
                               (∘ᵗ-congʳ (⟨⟩ᵢᵗ-projᵗ _ τ''))
                               (∘ᵗ-identityʳ _))))))))))))))))) ⟩
      uncurryᵗ
        (   T-alg-of-handlerᵀ
         ∘ᵗ (mapⁱˣᵗ
              (λ op →
                 mapⁱˣᵗ
                   (λ τ'' →
                        map⇒ᵗ
                          (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                          idᵗ
                     ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ
         (≡ᵗ-sym (∘ᵗ-assoc _ _ _))) ⟩
      uncurryᵗ
        ((    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
         ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (uncurryᵗ-mapʳ _ _) ⟩
      (uncurryᵗ
         (    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
      ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
      uncurryᵗ
         (    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
      ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵗ mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-cong (mapˣᵗ idᵗ) (Tᶠ-∘ᵗ _ _)))) ⟩
      uncurryᵗ
         (    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
      ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵗ Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-congˡ
         (≡ᵗ-trans
           (≡ᵗ-cong (λ f → mapˣᵗ f (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵗ Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))) (≡ᵗ-sym (∘ᵗ-identityʳ _)))
           (mapˣᵗ-∘ᵗ _ _ _ _)))) ⟩
      uncurryᵗ
         (    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
      ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
      ∘ᵗ (   mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
          ∘ᵗ mapˣᵗ idᵗ (Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ)))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)) ⟩
      uncurryᵗ
         (    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
      ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
      ∘ᵗ mapˣᵗ idᵗ (Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
      ∘ᵗ mapˣᵗ idᵗ strᵀ
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ
        (≡ᵗ-sym
          (≡ᵗ-trans
            (∘ᵗ-assoc _ _ _)
            (∘ᵗ-congʳ
              (≡ᵗ-trans
                (∘ᵗ-assoc _ _ _)
                (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _)))))) ⟩
      uncurryᵗ
         (    T-alg-of-handlerᵀ
          ∘ᵗ (mapⁱˣᵗ
               (λ op →
                  mapⁱˣᵗ
                    (λ τ'' →
                         map⇒ᵗ
                           (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                           idᵗ
                      ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))))
      ∘ᵗ (   mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
          ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
          ∘ᵗ mapˣᵗ idᵗ (Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
          ∘ᵗ mapˣᵗ idᵗ strᵀ)
      ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (
         begin
              mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
           ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
           ∘ᵗ mapˣᵗ idᵗ (Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ))
           ∘ᵗ mapˣᵗ idᵗ strᵀ
         ≡⟨ ≡ᵗ-trans
              (∘ᵗ-congʳ (∘ᵗ-congʳ (≡ᵗ-sym (mapˣᵗ-∘ᵗ _ _ _ _))))
              (≡ᵗ-trans
                (∘ᵗ-congʳ (≡ᵗ-sym (mapˣᵗ-∘ᵗ _ _ _ _)))
                (≡ᵗ-sym (mapˣᵗ-∘ᵗ _ _ _ _))) ⟩
           mapˣᵗ
             (⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵗ) ⟩ᵢᵗ ∘ᵗ idᵗ ∘ᵗ idᵗ ∘ᵗ idᵗ)
             (idᵗ ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵗ Tᶠ (mapˣᵗ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵗ) ∘ᵗ strᵀ)
         ≡⟨ ≡ᵗ-cong₂ mapˣᵗ
              (≡ᵗ-trans (∘ᵗ-congʳ (∘ᵗ-identityˡ _))
                (≡ᵗ-trans (∘ᵗ-congʳ (∘ᵗ-identityˡ _))
                  (≡ᵗ-trans (∘ᵗ-identityʳ _)
                    (≡ᵗ-trans
                      (≡ᵗ-trans
                        (≡-≡ᵗ (cong ⟨_⟩ᵢᵗ (fun-ext (λ op → ≡ᵗ-≡
                          (≡ᵗ-trans (≡-≡ᵗ (cong ⟨_⟩ᵢᵗ (fun-ext (λ τ'' → ≡ᵗ-≡ (≡ᵗ-sym (∘ᵗ-identityˡ _)))))) (⟨⟩ᵢᵗ-∘ᵗ _ _))))))
                        (⟨⟩ᵢᵗ-∘ᵗ _ _))
                      (≡ᵗ-sym (≡ᵗ-trans (∘ᵗ-congʳ (∘ᵗ-identityˡ _)) (∘ᵗ-congʳ (∘ᵗ-identityˡ _))))))))
              (≡ᵗ-trans
                (∘ᵗ-identityˡ _)
                (≡ᵗ-trans
                  (∘ᵗ-congʳ (≡ᵗ-sym
                    (≡ᵗ-trans
                      (∘ᵗ-congʳ (≡ᵗ-cong (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ))) (≡ᵗ-sym Tᶠ-idᵗ)))
                      (strᵀ-nat _ _))))
                  (≡ᵗ-sym (∘ᵗ-identityˡ _)))) ⟩
           mapˣᵗ
             (⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ ∘ᵗ idᵗ ∘ᵗ idᵗ ∘ᵗ ⟦ ρ ⟧ʳ)
             (idᵗ ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵗ strᵀ ∘ᵗ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ))
         ≡⟨ ≡ᵗ-trans
             (≡ᵗ-trans
               (mapˣᵗ-∘ᵗ _ _ _ _)
               (∘ᵗ-congʳ (mapˣᵗ-∘ᵗ _ _ _ _)))
             (∘ᵗ-congʳ (∘ᵗ-congʳ (mapˣᵗ-∘ᵗ _ _ _ _))) ⟩
              mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
           ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
           ∘ᵗ mapˣᵗ idᵗ strᵀ
           ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ)
         ∎)) ⟩
      uncurryᵗ
       (   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
       ∘ᵗ (   mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
           ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
           ∘ᵗ mapˣᵗ idᵗ strᵀ
           ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ))
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ
         (≡ᵗ-trans
           (∘ᵗ-assoc _ _ _)
           (∘ᵗ-congʳ
             (≡ᵗ-trans
               (∘ᵗ-assoc _ _ _)
               (∘ᵗ-congʳ
                 (∘ᵗ-assoc _ _ _))))) ⟩
      uncurryᵗ
       (   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
       ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ
       ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ)
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ≡ᵗ-sym
        (≡ᵗ-trans
          (∘ᵗ-assoc _ _ _)
          (∘ᵗ-congʳ
            (≡ᵗ-trans
              (∘ᵗ-assoc _ _ _)
              (∘ᵗ-congʳ (∘ᵗ-assoc _ _ _))))) ⟩
      (uncurryᵗ
       (   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
       ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ)
       ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ)
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
         ((uncurryᵗ
          (   T-alg-of-handlerᵀ
           ∘ᵗ mapⁱˣᵗ
                (λ op →
                   mapⁱˣᵗ
                     (λ τ'' →
                          map⇒ᵗ
                            (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                              ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                            idᵗ
                       ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
          ∘ᵗ mapˣᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ idᵗ)
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ)
       ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ)
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congˡ (≡ᵗ-sym (uncurryᵗ-mapʳ _ _))) ⟩
      (uncurryᵗ
       ((   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc))))
        ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ)
       ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ)
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (∘ᵗ-congˡ (≡ᵗ-cong uncurryᵗ (∘ᵗ-assoc _ _ _))) ⟩
      (uncurryᵗ
       (   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))
        ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ)
       ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ (mapˣᵗ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵗ)
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ
         (≡ᵗ-trans
           (≡ᵗ-sym (⟨⟩ᵗ-∘ᵗ _ _ _))
           (≡ᵗ-trans
             (≡ᵗ-cong₂ ⟨_,_⟩ᵗ
               (≡ᵗ-trans
                 (∘ᵗ-assoc _ _ _)
                 (≡ᵗ-trans
                   (∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _))
                   (≡ᵗ-trans
                     (∘ᵗ-identityʳ _)
                     (≡ᵗ-sym (∘ᵗ-identityˡ _)))))
               (≡ᵗ-trans
                 (∘ᵗ-assoc _ _ _)
                 (≡ᵗ-trans
                   (∘ᵗ-congʳ (⟨⟩ᵗ-sndᵗ  _ _))
                   (≡ᵗ-trans
                     (≡ᵗ-sym (⟨⟩ᵗ-∘ᵗ _ _ _))
                     (≡ᵗ-trans
                       (≡ᵗ-cong₂ ⟨_,_⟩ᵗ
                         (≡ᵗ-trans
                           (∘ᵗ-assoc _ _ _)
                           (≡ᵗ-trans
                             (∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _))
                             (η⊣-nat _)))
                         (≡ᵗ-trans
                           (∘ᵗ-assoc _ _ _)
                           (≡ᵗ-trans
                             (∘ᵗ-congʳ (⟨⟩ᵗ-sndᵗ _ _))
                             (∘ᵗ-identityˡ _))))
                       (⟨⟩ᵗ-∘ᵗ _ _ _))))))
             (⟨⟩ᵗ-∘ᵗ _ _ _))) ⟩
      (uncurryᵗ
       (   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))
        ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ)
       ∘ᵗ (   ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵗ ⟩ᵗ
           ∘ᵗ ⟦ ρ ⟧ʳ)
    ≡⟨ ≡ᵗ-trans
         (∘ᵗ-assoc _ _ _)
         (≡ᵗ-trans
           (∘ᵗ-congʳ
             (≡ᵗ-trans
               (∘ᵗ-assoc _ _ _)
               (≡ᵗ-trans
                 (∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))
                 (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))))
           (≡ᵗ-sym (∘ᵗ-assoc _ _ _))) ⟩
      (uncurryᵗ
       (   T-alg-of-handlerᵀ
        ∘ᵗ mapⁱˣᵗ
             (λ op →
                mapⁱˣᵗ
                  (λ τ'' →
                       map⇒ᵗ
                         (mapˣᵗ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵗ)))
                         idᵗ
                    ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×ᵗ-assoc)))
        ∘ᵗ ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ)
       ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵗ mapˣᵗ idᵗ strᵀ
       ∘ᵗ ⟨ idᵗ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵗ ⟩ᵗ)
      ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ ρ (unbox {A} {C} {τ} p V M) =
    begin
         ⟦ C-rename (cong-∷-ren ρ) M ⟧ᶜᵗ
      ∘ᵗ ⟨ idᵗ ,
              ε⊣
           ∘ᵗ ⟨ τ ⟩ᶠ ⟦ V-rename (ρ -ʳ τ) V ⟧ᵛᵗ
           ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ
    ≡⟨ ∘ᵗ-congˡ (C-rename≡∘ᵗ (cong-∷-ren {A = A} ρ) M) ⟩
         (⟦ M ⟧ᶜᵗ ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ)
      ∘ᵗ ⟨ idᵗ ,
              ε⊣
           ∘ᵗ ⟨ τ ⟩ᶠ ⟦ V-rename (ρ -ʳ τ) V ⟧ᵛᵗ
           ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-cong (⟨ idᵗ ,_⟩ᵗ) (∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-cong ⟨ τ ⟩ᶠ (V-rename≡∘ᵗ (ρ -ʳ τ) V))))) ⟩
         (⟦ M ⟧ᶜᵗ ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ)
      ∘ᵗ ⟨ idᵗ ,
              ε⊣
           ∘ᵗ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ -ʳ τ ⟧ʳ)
           ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ
    ≡⟨ ∘ᵗ-assoc _ _ _ ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵗ mapˣᵗ ⟦ ρ ⟧ʳ idᵗ
      ∘ᵗ ⟨ idᵗ ,
              ε⊣
           ∘ᵗ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ -ʳ τ ⟧ʳ)
           ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (
        begin
             ⟨ ⟦ ρ ⟧ʳ ∘ᵗ fstᵗ , idᵗ ∘ᵗ sndᵗ ⟩ᵗ
          ∘ᵗ ⟨ idᵗ ,
                  ε⊣
               ∘ᵗ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ -ʳ τ ⟧ʳ)
               ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ
        ≡⟨ ≡ᵗ-sym (⟨⟩ᵗ-∘ᵗ _ _ _) ⟩
             ⟨ (⟦ ρ ⟧ʳ ∘ᵗ fstᵗ) ∘ᵗ ⟨ idᵗ , ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ -ʳ τ ⟧ʳ) ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ ,
               (idᵗ ∘ᵗ sndᵗ) ∘ᵗ ⟨ idᵗ , ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ -ʳ τ ⟧ʳ) ∘ᵗ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵗ ⟩ᵗ
        ≡⟨ ≡ᵗ-cong₂ ⟨_,_⟩ᵗ
             (≡ᵗ-trans
               (∘ᵗ-assoc _ _ _)
               (≡ᵗ-trans
                 (∘ᵗ-congʳ (⟨⟩ᵗ-fstᵗ _ _))
                 (≡ᵗ-trans (∘ᵗ-identityʳ _) (≡ᵗ-sym (∘ᵗ-identityˡ _)))))
             (≡ᵗ-trans
               (∘ᵗ-assoc _ _ _)
               (≡ᵗ-trans
                 (∘ᵗ-identityˡ _)
                 (≡ᵗ-trans
                   (⟨⟩ᵗ-sndᵗ _ _)
                   (≡ᵗ-trans
                     (∘ᵗ-congʳ
                       (≡ᵗ-trans
                         (∘ᵗ-congˡ (⟨⟩-∘ᵗ _ _))
                         (≡ᵗ-trans
                           (∘ᵗ-assoc _ _ _)
                           (≡ᵗ-trans
                             (∘ᵗ-congʳ (≡ᵗ-sym (env-⟨⟩-ᶜ-nat τ p ρ)))
                             (≡ᵗ-sym (∘ᵗ-assoc _ _ _))))))
                     (≡ᵗ-sym (∘ᵗ-assoc _ _ _)))))) ⟩
          ⟨ idᵗ ∘ᵗ ⟦ ρ ⟧ʳ , (ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ env-⟨⟩-ᶜ τ p) ∘ᵗ ⟦ ρ ⟧ʳ ⟩ᵗ
        ≡⟨ ⟨⟩ᵗ-∘ᵗ _ _ _ ⟩
          ⟨ idᵗ , ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ env-⟨⟩-ᶜ τ p ⟩ᵗ ∘ᵗ ⟦ ρ ⟧ʳ
        ∎) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵗ ⟨ idᵗ ,
              ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
           ∘ᵗ env-⟨⟩-ᶜ τ p ⟩ᵗ
      ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵗ ⟨ idᵗ ,
                  ε⊣ ∘ᵗ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
               ∘ᵗ env-⟨⟩-ᶜ τ p ⟩ᵗ)
      ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵗ ρ (delay τs M) =
    begin
      delayᵀ τs ∘ᵗ [ τs ]ᶠ ⟦ C-rename (cong-⟨⟩-ren ρ) M ⟧ᶜᵗ ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ (≡ᵗ-cong [ τs ]ᶠ (C-rename≡∘ᵗ (cong-⟨⟩-ren ρ) M))) ⟩
      delayᵀ τs ∘ᵗ [ τs ]ᶠ (⟦ M ⟧ᶜᵗ ∘ᵗ ⟦ (cong-⟨⟩-ren ρ) ⟧ʳ) ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congˡ ([]-∘ᵗ (⟨ τs ⟩ᶠ ⟦ ρ ⟧ʳ) ⟦ M ⟧ᶜᵗ)) ⟩
      delayᵀ τs ∘ᵗ ([ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵗ [ τs ]ᶠ (⟨ τs ⟩ᶠ ⟦ ρ ⟧ʳ)) ∘ᵗ η⊣
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-assoc _ _ _) ⟩
      delayᵀ τs ∘ᵗ [ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵗ ([ τs ]ᶠ (⟨ τs ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵗ η⊣)
    ≡⟨ ∘ᵗ-congʳ (∘ᵗ-congʳ (η⊣-nat _)) ⟩
      delayᵀ τs ∘ᵗ [ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵗ (η⊣ ∘ᵗ ⟦ ρ ⟧ʳ)
    ≡⟨ ∘ᵗ-congʳ (≡ᵗ-sym (∘ᵗ-assoc _ _ _)) ⟩
      delayᵀ τs ∘ᵗ ([ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵗ η⊣) ∘ᵗ ⟦ ρ ⟧ʳ
    ≡⟨ ≡ᵗ-sym (∘ᵗ-assoc _ _ _) ⟩
      (delayᵀ τs ∘ᵗ [ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵗ η⊣) ∘ᵗ ⟦ ρ ⟧ʳ
    ∎
