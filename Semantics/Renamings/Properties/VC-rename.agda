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

  V-rename≡∘ᵐ : ∀ {Γ Γ' A}
              → (ρ : Ren Γ Γ')
              → (V : Γ ⊢V⦂ A)
              → ⟦ V-rename ρ V ⟧ᵛᵗ
             ≡ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ

  V-rename≡∘ᵐ {Γ} {Γ'} {A} ρ (var {τ = τ} x) =
    begin
      var-in-env (proj₂ (proj₂ (var-rename ρ x)))
    ≡⟨ var-in-env∘var-rename≡var-rename∘ᵐ⟦⟧ʳ ρ x ⟩
      var-in-env x ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵐ ρ (const c) =
    begin
      constᵐ c ∘ᵐ terminalᵐ
    ≡⟨ ∘ᵐ-congʳ (sym terminalᵐ-unique) ⟩
      constᵐ c ∘ᵐ (terminalᵐ ∘ᵐ ⟦ ρ ⟧ʳ)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      (constᵐ c ∘ᵐ terminalᵐ) ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵐ ρ ⋆ =
    begin
      terminalᵐ
    ≡⟨ sym terminalᵐ-unique ⟩
      terminalᵐ ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵐ ρ (lam {A} M) =
    begin
      curryᵐ ⟦ C-rename (cong-∷-ren ρ) M ⟧ᶜᵗ
    ≡⟨ cong curryᵐ (C-rename≡∘ᵐ (cong-∷-ren ρ) M) ⟩
      curryᵐ (⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ cong-∷-ren {A = A} ρ ⟧ʳ)
    ≡⟨⟩
      curryᵐ (⟦ M ⟧ᶜᵗ ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ)
    ≡⟨ curryᵐ-mapˣᵐ ⟦ M ⟧ᶜᵗ ⟦ ρ ⟧ʳ idᵐ ⟩
      map⇒ᵐ idᵐ idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵐ-congˡ map⇒ᵐ-identity ⟩
      idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵐ-identityˡ _ ⟩
      curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  V-rename≡∘ᵐ ρ (box {τ = τ} V) =
    begin
      [ τ ]ᶠ ⟦ V-rename (cong-⟨⟩-ren ρ) V ⟧ᵛᵗ ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congˡ (cong [ τ ]ᶠ (V-rename≡∘ᵐ (cong-⟨⟩-ren ρ) V)) ⟩
      [ τ ]ᶠ (⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ cong-⟨⟩-ren ρ ⟧ʳ) ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congˡ ([]-∘ᵐ ⟦ cong-⟨⟩-ren ρ ⟧ʳ ⟦ V ⟧ᵛᵗ) ⟩
      ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ [ τ ]ᶠ ⟦ cong-⟨⟩-ren ρ ⟧ʳ) ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ ([ τ ]ᶠ ⟦ cong-⟨⟩-ren ρ ⟧ʳ ∘ᵐ η⊣)
    ≡⟨⟩
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (η⊣-nat _) ⟩
      [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣ ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      ([ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣) ∘ᵐ ⟦ ρ ⟧ʳ
    ∎

  C-rename≡∘ᵐ : ∀ {Γ Γ' C}
              → (ρ : Ren Γ Γ')
              → (M : Γ ⊢C⦂ C)
              → ⟦ C-rename ρ M ⟧ᶜᵗ
             ≡ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ

  C-rename≡∘ᵐ ρ (return V) = 
    begin
      ηᵀ ∘ᵐ ⟦ V-rename ρ V ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-rename≡∘ᵐ ρ V) ⟩
      ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ) ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ {Γ} {Γ'} ρ (_;_ {A} {B} {τ} {τ'} M N) =
    begin
         μᵀ
      ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) N ⟧ᶜᵗ
      ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵐ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ C-rename ρ M ⟧ᶜᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ η⊣ ,_⟩ᵐ (C-rename≡∘ᵐ ρ M)))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) N ⟧ᶜᵗ
      ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵐ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong Tᶠ (C-rename≡∘ᵐ (cong-∷-ren (cong-⟨⟩-ren ρ)) N))) ⟩
         μᵀ
      ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ ⟦ cong-∷-ren {A = A} (cong-⟨⟩-ren ρ) ⟧ʳ)
      ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵐ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (Tᶠ-∘ᵐ _ _)) ⟩
         μᵀ
      ∘ᵐ (   Tᶠ (⟦ N ⟧ᶜᵗ)
          ∘ᵐ Tᶠ ⟦ cong-∷-ren {A = A} (cong-⟨⟩-ren ρ) ⟧ʳ)
      ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ' ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵐ ⟨ η⊣ {⟦ Γ' ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ)
      ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (
           begin
                Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ)
             ∘ᵐ strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
                (   Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ)
                 ∘ᵐ strᵀ)
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ ∘ᵐ-congˡ (sym (strᵀ-nat _ _)) ⟩
                (   strᵀ
                 ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) (Tᶠ idᵐ))
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
                strᵀ
             ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) (Tᶠ idᵐ)
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ))) Tᶠ-idᵐ)) ⟩
                strᵀ
             ∘ᵐ mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨⟩
                strᵀ
             ∘ᵐ ⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) ⟩
                strᵀ
             ∘ᵐ ⟨ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵐ fstᵐ) ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ,
                  (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ η⊣ {τ = τ} , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
           ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
               (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
               (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (⟨⟩ᵐ-sndᵐ _ _)))) ⟩
                strᵀ
             ∘ᵐ ⟨ [ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵐ η⊣ ,
                  ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ ∘ᵐ-congʳ (cong ⟨_, ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ (η⊣-nat _)) ⟩
                strᵀ
             ∘ᵐ ⟨ η⊣ ∘ᵐ ⟦ ρ ⟧ʳ ,
                  ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
           ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
                strᵀ
             ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
             ∘ᵐ ⟦ ρ ⟧ʳ
           ∎)) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
      ∘ᵐ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ
      ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _))) ⟩
         μᵀ
      ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
      ∘ᵐ (   strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
          ∘ᵐ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
      ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
         μᵀ
      ∘ᵐ (Tᶠ ⟦ N ⟧ᶜᵗ
          ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
          ∘ᵐ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
      ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   μᵀ
          ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
          ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ} {⟦ A ⟧ᵛ}
          ∘ᵐ ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
      ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ ρ (V · W) = 
    begin
      appᵐ ∘ᵐ ⟨ ⟦ V-rename ρ V ⟧ᵛᵗ , ⟦ V-rename ρ W ⟧ᵛᵗ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (V-rename≡∘ᵐ ρ V) (V-rename≡∘ᵐ ρ W))
     ⟩
      appᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
      appᵐ ∘ᵐ (⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ ∘ᵐ ⟦ ρ ⟧ʳ)
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      (appᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ) ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ ρ (absurd V) =
    begin
      initialᵐ ∘ᵐ ⟦ V-rename ρ V ⟧ᵛᵗ
    ≡⟨ ∘ᵐ-congʳ (V-rename≡∘ᵐ ρ V) ⟩
      initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      (initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ) ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ ρ (perform op V M) =
    begin
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V-rename ρ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
        (∘ᵐ-congʳ (V-rename≡∘ᵐ ρ V))
        (∘ᵐ-congʳ (∘ᵐ-congˡ (cong
                              (λ f → [ op-time op ]ᶠ (curryᵐ f))
                              (C-rename≡∘ᵐ (cong-∷-ren (cong-⟨⟩-ren ρ)) M))))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ
                (curryᵐ (   ⟦ M ⟧ᶜᵗ
                         ∘ᵐ ⟦ (cong-∷-ren {A = type-of-gtype (arity op)} (cong-⟨⟩-ren ρ)) ⟧ʳ) )
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong [ op-time op ]ᶠ (curryᵐ-mapˣᵐ _ _ _))))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (map⇒ᵐ idᵐ idᵐ ∘ᵐ curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ)
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong [ op-time op ]ᶠ (trans (∘ᵐ-congˡ map⇒ᵐ-identity) (∘ᵐ-identityˡ _)))))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ)
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
        ([]-∘ᵐ (⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ) (curryᵐ ⟦ M ⟧ᶜᵗ))))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ (   [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
               ∘ᵐ [ op-time op ]ᶠ(⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ))
           ∘ᵐ η⊣ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ (   [ op-time op ]ᶠ(⟨ op-time op ⟩ᶠ ⟦ ρ ⟧ʳ)
               ∘ᵐ η⊣) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,_⟩ᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-nat _)))) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ (   η⊣ 
               ∘ᵐ ⟦ ρ ⟧ʳ) ⟩ᵐ
    ≡⟨⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ ⟧ʳ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ 
           ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ
                  (sym (∘ᵐ-assoc _ _ _))
                  (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
         opᵀ op
      ∘ᵐ ⟨    (   ⟦⟧ᵛ-⟦⟧ᵍ (param op)
               ∘ᵐ ⟦ V ⟧ᵛᵗ)
           ∘ᵐ ⟦ ρ ⟧ʳ ,
              (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
               ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
               ∘ᵐ η⊣)
           ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
         opᵀ op
      ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
              [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
           ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
           ∘ᵐ η⊣ ⟩ᵐ
      ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      (   opᵀ op
       ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
               [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
            ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
            ∘ᵐ η⊣ ⟩ᵐ)
      ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ {Γ} {Γ'} ρ (handle_`with_`in {A} {B} {τ} {τ'} M H N) =
    begin
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                 (λ τ'' →
                    map⇒ᵐ
                    (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                     ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                    idᵐ
                    ∘ᵐ
                    curryᵐ
                    (   ⟦ C-rename (cong-∷-ren (cong-∷-ren ρ)) (H op τ'') ⟧ᶜᵗ
                     ∘ᵐ ×ᵐ-assoc)))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren ρ)) N ⟧ᶜᵗ)
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ C-rename ρ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong₂ _∘ᵐ_
         (cong (mapˣᵐ idᵐ) (cong Tᶠ (C-rename≡∘ᵐ ((cong-∷-ren (cong-⟨⟩-ren ρ))) N)))
         (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (cong ⟨ η⊣ ,_⟩ᵐ (C-rename≡∘ᵐ ρ M))))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                 (λ τ'' →
                    map⇒ᵐ
                    (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                     ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                    idᵐ
                    ∘ᵐ
                    curryᵐ
                    (   ⟦ C-rename (cong-∷-ren (cong-∷-ren ρ)) (H op τ'') ⟧ᶜᵗ
                     ∘ᵐ ×ᵐ-assoc)))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
         (cong mapⁱˣᵐ (fun-ext (λ op → cong mapⁱˣᵐ (fun-ext (λ τ'' →
           (∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congˡ
                (C-rename≡∘ᵐ (cong-∷-ren (cong-∷-ren ρ)) (H op τ''))))))))))))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                   (λ τ'' →
                     map⇒ᵐ
                     (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                      ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                     idᵐ
                     ∘ᵐ
                     curryᵐ
                     (   (   ⟦ H op τ'' ⟧ᶜᵗ
                          ∘ᵐ ⟦ (cong-∷-ren {A = [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')}
                                 (cong-∷-ren {A = type-of-gtype (param op)} ρ)) ⟧ʳ)
                      ∘ᵐ ×ᵐ-assoc)))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                   (λ τ'' →
                        map⇒ᵐ
                          (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                          idᵐ
                     ∘ᵐ curryᵐ
                          (   (   ⟦ H op τ'' ⟧ᶜᵗ
                               ∘ᵐ mapˣᵐ (mapˣᵐ ⟦ ρ ⟧ʳ idᵐ) idᵐ)
                           ∘ᵐ ×ᵐ-assoc)))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong mapⁱˣᵐ (fun-ext (λ op → cong mapⁱˣᵐ (fun-ext (λ τ'' →
          (∘ᵐ-congʳ (
            begin
              curryᵐ ((⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ mapˣᵐ (mapˣᵐ ⟦ ρ ⟧ʳ idᵐ) idᵐ) ∘ᵐ ×ᵐ-assoc)
            ≡⟨ cong curryᵐ (∘ᵐ-assoc _ _ _) ⟩
              curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ (mapˣᵐ (mapˣᵐ ⟦ ρ ⟧ʳ idᵐ) idᵐ ∘ᵐ ×ᵐ-assoc))
            ≡⟨ cong curryᵐ (∘ᵐ-congʳ (mapˣᵐ-×ᵐ-assoc _ _ _)) ⟩
              curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ (×ᵐ-assoc ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ idᵐ idᵐ)))
            ≡⟨ cong curryᵐ (sym (∘ᵐ-assoc _ _ _)) ⟩
              curryᵐ ((⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc) ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ idᵐ idᵐ))
            ≡⟨ curryᵐ-mapˣᵐ _ _ _ ⟩
              map⇒ᵐ (mapˣᵐ idᵐ idᵐ) idᵐ ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc) ∘ᵐ ⟦ ρ ⟧ʳ
            ≡⟨ ∘ᵐ-congˡ (cong (λ f → map⇒ᵐ f idᵐ) (sym
                 (⟨⟩ᵐ-unique _ _ _
                   (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
                   (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))))) ⟩
              map⇒ᵐ idᵐ idᵐ ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc) ∘ᵐ ⟦ ρ ⟧ʳ
            ≡⟨ ∘ᵐ-congˡ map⇒ᵐ-identity ⟩
              idᵐ ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc) ∘ᵐ ⟦ ρ ⟧ʳ
            ≡⟨ ∘ᵐ-identityˡ _ ⟩
              curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc) ∘ᵐ ⟦ ρ ⟧ʳ
            ∎)))))))))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                   (λ τ'' →
                        map⇒ᵐ
                          (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                          idᵐ
                     ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)
                     ∘ᵐ ⟦ ρ ⟧ʳ))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
         (cong mapⁱˣᵐ (fun-ext (λ op → cong mapⁱˣᵐ (fun-ext (λ τ'' → (sym (∘ᵐ-assoc _ _ _)))))))))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                   (λ τ'' →
                        (   map⇒ᵐ
                             (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                               ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                             idᵐ
                         ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))
                     ∘ᵐ ⟦ ρ ⟧ʳ))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
         (cong mapⁱˣᵐ (fun-ext (λ op → (mapⁱˣᵐ-∘ᵐ _ _))))))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ (  mapⁱˣᵐ
                (λ op →
                   mapⁱˣᵐ
                     (λ τ'' →
                          map⇒ᵐ
                            (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                              ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                            idᵐ
                       ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))
                       ∘ᵐ mapⁱˣᵐ (λ τ'' → ⟦ ρ ⟧ʳ)))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ
         (mapⁱˣᵐ-∘ᵐ _ _)))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ ((  mapⁱˣᵐ
                (λ op →
                   mapⁱˣᵐ
                     (λ τ'' →
                          map⇒ᵐ
                            (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                              ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                            idᵐ
                       ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
            ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ'' → ⟦ ρ ⟧ʳ)))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ (mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                   (λ τ'' →
                        map⇒ᵐ
                          (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                          idᵐ
                     ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
         ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ'' → ⟦ ρ ⟧ʳ))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ
         (trans
           (sym (⟨⟩ᵢᵐ-∘ᵐ _ _))
           (cong ⟨_⟩ᵢᵐ (fun-ext λ op →
             (trans
                 (∘ᵐ-assoc _ _ _)
                   (trans
                     (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ op))
                     (trans
                       (sym (⟨⟩ᵢᵐ-∘ᵐ _ _))
                       (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' →
                         (trans
                             (∘ᵐ-assoc _ _ _)
                             (trans
                               (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ τ''))
                               (∘ᵐ-identityʳ _))))))))))))))) ⟩
      uncurryᵐ
        (   T-alg-of-handlerᵀ
         ∘ᵐ (mapⁱˣᵐ
              (λ op →
                 mapⁱˣᵐ
                   (λ τ'' →
                        map⇒ᵐ
                          (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                            ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                          idᵐ
                     ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ
         (sym (∘ᵐ-assoc _ _ _))) ⟩
      uncurryᵐ
        ((    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
         ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (uncurryᵐ-mapˣᵐʳ _ _) ⟩
      (uncurryᵐ
         (    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
      ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
      uncurryᵐ
         (    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
      ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong (mapˣᵐ idᵐ) (Tᶠ-∘ᵐ _ _)))) ⟩
      uncurryᵐ
         (    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
      ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
         (trans
           (cong (λ f → mapˣᵐ f (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))) (sym (∘ᵐ-identityʳ _)))
           (mapˣᵐ-∘ᵐ _ _ _ _)))) ⟩
      uncurryᵐ
         (    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
      ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
      ∘ᵐ (   mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
          ∘ᵐ mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ)))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
      uncurryᵐ
         (    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
      ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
      ∘ᵐ mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
      ∘ᵐ mapˣᵐ idᵐ strᵀ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ
        (sym
          (trans
            (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ
              (trans
                (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
      uncurryᵐ
         (    T-alg-of-handlerᵀ
          ∘ᵐ (mapⁱˣᵐ
               (λ op →
                  mapⁱˣᵐ
                    (λ τ'' →
                         map⇒ᵐ
                           (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                             ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                           idᵐ
                      ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))))
      ∘ᵐ (   mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
          ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
          ∘ᵐ mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
          ∘ᵐ mapˣᵐ idᵐ strᵀ)
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (
         begin
              mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
           ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
           ∘ᵐ mapˣᵐ idᵐ (Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ))
           ∘ᵐ mapˣᵐ idᵐ strᵀ
         ≡⟨ trans
              (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))))
              (trans
                (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)))
                (sym (mapˣᵐ-∘ᵐ _ _ _ _))) ⟩
           mapˣᵐ
             (⟨ (λ op → ⟨ (λ τ'' → ⟦ ρ ⟧ʳ) ⟩ᵢᵐ) ⟩ᵢᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
             (idᵐ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ Tᶠ (mapˣᵐ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ) idᵐ) ∘ᵐ strᵀ)
         ≡⟨ cong₂ mapˣᵐ
              (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                  (trans (∘ᵐ-identityʳ _)
                    (trans
                      (trans
                        (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → 
                          trans (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ'' → (sym (∘ᵐ-identityˡ _))))) (⟨⟩ᵢᵐ-∘ᵐ _ _))))
                        (⟨⟩ᵢᵐ-∘ᵐ _ _))
                      (sym (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))))
              (trans
                (∘ᵐ-identityˡ _)
                (trans
                  (∘ᵐ-congʳ (sym
                    (trans
                      (∘ᵐ-congʳ (cong (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ))) (sym Tᶠ-idᵐ)))
                      (strᵀ-nat _ _))))
                  (sym (∘ᵐ-identityˡ _)))) ⟩
           mapˣᵐ
             (⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ ∘ᵐ ⟦ ρ ⟧ʳ)
             (idᵐ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ))
         ≡⟨ trans
             (trans
               (mapˣᵐ-∘ᵐ _ _ _ _)
               (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _)))
             (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _))) ⟩
              mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
           ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
           ∘ᵐ mapˣᵐ idᵐ strᵀ
           ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ)
         ∎)) ⟩
      uncurryᵐ
       (   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
       ∘ᵐ (   mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
           ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
           ∘ᵐ mapˣᵐ idᵐ strᵀ
           ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ))
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ
         (trans
           (∘ᵐ-assoc _ _ _)
           (∘ᵐ-congʳ
             (trans
               (∘ᵐ-assoc _ _ _)
               (∘ᵐ-congʳ
                 (∘ᵐ-assoc _ _ _))))) ⟩
      uncurryᵐ
       (   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
       ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ
       ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ)
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ sym
        (trans
          (∘ᵐ-assoc _ _ _)
          (∘ᵐ-congʳ
            (trans
              (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
      (uncurryᵐ
       (   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
       ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ)
       ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ)
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-assoc _ _ _)) ⟩
         ((uncurryᵐ
          (   T-alg-of-handlerᵀ
           ∘ᵐ mapⁱˣᵐ
                (λ op →
                   mapⁱˣᵐ
                     (λ τ'' →
                          map⇒ᵐ
                            (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                              ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                            idᵐ
                       ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
          ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ)
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ)
       ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ)
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (sym (uncurryᵐ-mapˣᵐʳ _ _))) ⟩
      (uncurryᵐ
       ((   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc))))
        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ)
       ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ)
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-assoc _ _ _))) ⟩
      (uncurryᵐ
       (   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))
        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ)
       ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ (mapˣᵐ ([ τ ]ᶠ (⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ)) idᵐ)
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ
         (trans
           (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
           (trans
             (cong₂ ⟨_,_⟩ᵐ
               (trans
                 (∘ᵐ-assoc _ _ _)
                 (trans
                   (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                   (trans
                     (∘ᵐ-identityʳ _)
                     (sym (∘ᵐ-identityˡ _)))))
               (trans
                 (∘ᵐ-assoc _ _ _)
                 (trans
                   (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ  _ _))
                   (trans
                     (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                     (trans
                       (cong₂ ⟨_,_⟩ᵐ
                         (trans
                           (∘ᵐ-assoc _ _ _)
                           (trans
                             (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                             (η⊣-nat _)))
                         (trans
                           (∘ᵐ-assoc _ _ _)
                           (trans
                             (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                             (∘ᵐ-identityˡ _))))
                       (⟨⟩ᵐ-∘ᵐ _ _ _))))))
             (⟨⟩ᵐ-∘ᵐ _ _ _))) ⟩
      (uncurryᵐ
       (   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))
        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ)
       ∘ᵐ (   ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
           ∘ᵐ ⟦ ρ ⟧ʳ)
    ≡⟨ trans
         (∘ᵐ-assoc _ _ _)
         (trans
           (∘ᵐ-congʳ
             (trans
               (∘ᵐ-assoc _ _ _)
               (trans
                 (∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)))
                 (sym (∘ᵐ-assoc _ _ _)))))
           (sym (∘ᵐ-assoc _ _ _))) ⟩
      (uncurryᵐ
       (   T-alg-of-handlerᵀ
        ∘ᵐ mapⁱˣᵐ
             (λ op →
                mapⁱˣᵐ
                  (λ τ'' →
                       map⇒ᵐ
                         (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                           ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
                         idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))
        ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
       ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
       ∘ᵐ mapˣᵐ idᵐ strᵀ
       ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)
      ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ ρ (unbox {A} {C} {τ} p V M) =
    begin
         ⟦ C-rename (cong-∷-ren ρ) M ⟧ᶜᵗ
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V-rename (ρ -ʳ τ) V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ
    ≡⟨ ∘ᵐ-congˡ (C-rename≡∘ᵐ (cong-∷-ren {A = A} ρ) M) ⟩
         (⟦ M ⟧ᶜᵗ ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ)
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V-rename (ρ -ʳ τ) V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (cong (⟨ idᵐ ,_⟩ᵐ) (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ ⟩ᶠ (V-rename≡∘ᵐ (ρ -ʳ τ) V))))) ⟩
         (⟦ M ⟧ᶜᵗ ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ)
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ -ʳ τ ⟧ʳ)
           ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ
    ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
      ∘ᵐ ⟨ idᵐ ,
              ε⊣
           ∘ᵐ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ -ʳ τ ⟧ʳ)
           ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ
    ≡⟨ ∘ᵐ-congʳ (
        begin
             ⟨ ⟦ ρ ⟧ʳ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣
               ∘ᵐ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ -ʳ τ ⟧ʳ)
               ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ
        ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
             ⟨ (⟦ ρ ⟧ʳ ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ -ʳ τ ⟧ʳ) ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ ,
               (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ (⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ ρ -ʳ τ ⟧ʳ) ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ)) ⟩ᵐ ⟩ᵐ
        ≡⟨ cong₂ ⟨_,_⟩ᵐ
             (trans
               (∘ᵐ-assoc _ _ _)
               (trans
                 (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                 (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))))
             (trans
               (∘ᵐ-assoc _ _ _)
               (trans
                 (∘ᵐ-identityˡ _)
                 (trans
                   (⟨⟩ᵐ-sndᵐ _ _)
                   (trans
                     (∘ᵐ-congʳ
                       (trans
                         (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _))
                         (trans
                           (∘ᵐ-assoc _ _ _)
                           (trans
                             (∘ᵐ-congʳ (sym (env-⟨⟩-ᶜ-nat τ p ρ)))
                             (sym (∘ᵐ-assoc _ _ _))))))
                     (sym (∘ᵐ-assoc _ _ _)))))) ⟩
          ⟨ idᵐ ∘ᵐ ⟦ ρ ⟧ʳ , (ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p) ∘ᵐ ⟦ ρ ⟧ʳ ⟩ᵐ
        ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
          ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ ∘ᵐ ⟦ ρ ⟧ʳ
        ∎) ⟩
         ⟦ M ⟧ᶜᵗ
      ∘ᵐ ⟨ idᵐ ,
              ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
           ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ
      ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (   ⟦ M ⟧ᶜᵗ
          ∘ᵐ ⟨ idᵐ ,
                  ε⊣ ∘ᵐ ⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ
               ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ)
      ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
  C-rename≡∘ᵐ ρ (delay τs M) =
    begin
      delayᵀ τs ∘ᵐ [ τs ]ᶠ ⟦ C-rename (cong-⟨⟩-ren ρ) M ⟧ᶜᵗ ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ τs ]ᶠ (C-rename≡∘ᵐ (cong-⟨⟩-ren ρ) M))) ⟩
      delayᵀ τs ∘ᵐ [ τs ]ᶠ (⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ (cong-⟨⟩-ren ρ) ⟧ʳ) ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ (⟨ τs ⟩ᶠ ⟦ ρ ⟧ʳ) ⟦ M ⟧ᶜᵗ)) ⟩
      delayᵀ τs ∘ᵐ ([ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ [ τs ]ᶠ (⟨ τs ⟩ᶠ ⟦ ρ ⟧ʳ)) ∘ᵐ η⊣
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
      delayᵀ τs ∘ᵐ [ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ ([ τs ]ᶠ (⟨ τs ⟩ᶠ ⟦ ρ ⟧ʳ) ∘ᵐ η⊣)
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-nat _)) ⟩
      delayᵀ τs ∘ᵐ [ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ (η⊣ ∘ᵐ ⟦ ρ ⟧ʳ)
    ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
      delayᵀ τs ∘ᵐ ([ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣) ∘ᵐ ⟦ ρ ⟧ʳ
    ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
      (delayᵀ τs ∘ᵐ [ τs ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣) ∘ᵐ ⟦ ρ ⟧ʳ
    ∎
