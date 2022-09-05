----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

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

module Semantics.Renamings.Properties.Rename where

mutual

  V-rename≡∘ᵗ : ∀ {Γ Γ' A}
              → (ρ : Ren Γ Γ')
              → (V : Γ ⊢V⦂ A)
              → ⟦ V-rename ρ V ⟧ᵛᵗ
             ≡ᵗ ⟦ V ⟧ᵛᵗ ∘ᵗ ⟦ ρ ⟧ʳ

  V-rename≡∘ᵗ ρ (var x) = {!!}
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
    ≡⟨ ≡-≡ᵗ (cong curryᵗ (≡ᵗ-≡ (C-rename≡∘ᵗ (cong-∷-ren ρ) M))) ⟩
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
  V-rename≡∘ᵗ ρ (box V) = {!!}

-- curryᵗ-mapˣᵗ

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
  C-rename≡∘ᵗ ρ (M ; N) = {!!}
  C-rename≡∘ᵗ ρ (V · W) = 
    begin
      appᵗ ∘ᵗ ⟨ ⟦ V-rename ρ V ⟧ᵛᵗ , ⟦ V-rename ρ W ⟧ᵛᵗ ⟩ᵗ
    ≡⟨ ∘ᵗ-congʳ (≡-≡ᵗ
         (cong₂ ⟨_,_⟩ᵗ
           (≡ᵗ-≡ (V-rename≡∘ᵗ ρ V))
           (≡ᵗ-≡ (V-rename≡∘ᵗ ρ W))))
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
  C-rename≡∘ᵗ ρ (perform op V M) = {!!}
  C-rename≡∘ᵗ ρ (handle M `with H `in N) = {!!}
  C-rename≡∘ᵗ ρ (unbox p V M) = {!!}
  C-rename≡∘ᵗ ρ (delay τs refl M) = {!!}
