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
    ⟨ split-env p ∘ᵐ fstᵐ ,
      idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ cong ⟨_, idᵐ ∘ᵐ sndᵐ ⟩ᵐ (∘ᵐ-congˡ (split-env-eq-ren p)) ⟩
    ⟨ (split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ ⟦ eq-ren (split-≡ p) ⟧ʳ) ∘ᵐ fstᵐ ,
      idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ {!!} ⟩
    ⟨   (split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ)
     ∘ᵐ ⟦ eq-ren (cong (_∷ A) (split-≡ p)) ⟧ʳ
    ,
        (idᵐ ∘ᵐ sndᵐ)
     ∘ᵐ ⟦ eq-ren (cong (_∷ A) (split-≡ p)) ⟧ʳ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       ⟨ split-env {Γ' = Γ'} {Γ'' = Γ''} (≡-split refl) ∘ᵐ fstᵐ ,
         idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟦ eq-ren (cong (_∷ A) (split-≡ p)) ⟧ʳ
  ∎
split-env-eq-ren {.(_ ⟨ _ ⟩)} {Γ'} {.(_ ⟨ _ ⟩)} (split-⟨⟩ p) = {!!}

