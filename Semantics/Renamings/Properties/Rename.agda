----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

module Semantics.Renamings.Properties.Rename where

open import Function

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Semantics.TSets
open import Semantics.Modality.Past
open import Semantics.Modality.Future
open import Semantics.Modality.Adjunction
open import Semantics.Monad
open import Semantics.Interpretation
open import Semantics.Renamings.Core

open import Util.Equality
open import Util.Operations
open import Util.Time

mutual

  {-
  var-in-env∘ᵗ⟦⟧ʳ≡⟦⟧ʳ∘ᵗvar-in-env : ∀ {Γ Γ' A τ}
                                  → (ρ : Ren Γ Γ')
                                  → (x : A ∈[ τ ] Γ)
                                  →    var-in-env x
                                    ∘ᵗ ⟦ ρ ⟧ʳ
                                 ≡ᵗ    {!⟦ ? ⟧ʳ!}
                                    ∘ᵗ var-in-env (proj₂ (proj₂ (var-rename ρ x)))
  var-in-env∘ᵗ⟦⟧ʳ≡⟦⟧ʳ∘ᵗvar-in-env ρ x = {!!}
  -}

  V-rename≡∘ᵗ : ∀ {Γ Γ' A}
              → (ρ : Ren Γ Γ')
              → (V : Γ ⊢V⦂ A)
              → ⟦ V-rename ρ V ⟧ᵛᵗ
             ≡ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ

  V-rename≡∘ᵗ {Γ} {Γ'} {A} ρ (var {τ = τ} x) =
    begin
         ε-⟨⟩
      ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split (proj₂ (proj₂ (var-rename ρ x))))))
      ∘ᵗ var-in-env (proj₂ (proj₂ (var-rename ρ x)))
    ≡⟨ {!!} ⟩
         (   ε-⟨⟩
          ∘ᵗ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))) ∘ᵗ var-in-env x)
      ∘ᵗ ⟦ ρ ⟧ʳ
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
    {!!}
  {-
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
  -}
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
  C-rename≡∘ᵗ ρ (handle M `with H `in N) = {!!}
  C-rename≡∘ᵗ ρ (unbox p V M) = {!!}
  C-rename≡∘ᵗ ρ (delay τs M) =
    {!!}
  {-
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
  -}
