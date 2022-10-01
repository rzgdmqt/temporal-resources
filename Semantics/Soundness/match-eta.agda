-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.match-eta (Mod : Model) where

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

match-eta-sound : ∀ {Γ A B C}
                → (V : Γ ⊢V⦂ A |×| B)
                → (M : Γ ∷ A |×| B ⊢C⦂ C)
                → ⟦ match V `in
                      (C-rename (exch-ren ∘ʳ wk-ren ∘ʳ exch-ren ∘ʳ wk-ren)
                        M [ Hd ↦ ⦉ var (Tl-∷ Hd) , var Hd ⦊ ]c) ⟧ᶜᵗ
                ≡ ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ

match-eta-sound {Γ} {A} {B} {C} V M =
  begin
       ⟦ C-rename
           ((var-ren (Tl-∷ Hd) ∘ʳ
             cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
            ∘ʳ
            wk-ren ∘ʳ
            (var-ren (Tl-∷ Hd) ∘ʳ
             cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
            ∘ʳ wk-ren) M [ Hd ↦ ⦉ var (Tl-∷ Hd) , var Hd ⦊ ]c ⟧ᶜᵗ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ
      (C-subst≡∘ᵐ
         (C-rename
           ((var-ren (Tl-∷ Hd) ∘ʳ
             cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
            ∘ʳ
            wk-ren ∘ʳ
            (var-ren (Tl-∷ Hd) ∘ʳ
             cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
            ∘ʳ wk-ren) M) Hd (⦉ var (Tl-∷ Hd) , var Hd ⦊)) ⟩
       (   ⟦ C-rename
              ((var-ren (Tl-∷ Hd) ∘ʳ
                cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
               ∘ʳ
               wk-ren ∘ʳ
               (var-ren (Tl-∷ Hd) ∘ʳ
                cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
               ∘ʳ wk-ren) M ⟧ᶜᵗ
        ∘ᵐ idᵐ
        ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ idᵐ)
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       ⟦ C-rename
          ((var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ
           wk-ren ∘ʳ
           (var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ wk-ren) M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
       ⟦ C-rename
          ((var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ
           wk-ren ∘ʳ
           (var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ wk-ren) M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) ⟩
       ⟦ C-rename
          ((var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ
           wk-ren ∘ʳ
           (var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ wk-ren) M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ
       (C-rename≡∘ᵐ
         ((var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ
           wk-ren ∘ʳ
           (var-ren (Tl-∷ Hd) ∘ʳ
            cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
           ∘ʳ wk-ren) M) ⟩
       (   ⟦ M ⟧ᶜᵗ
        ∘ᵐ (  (   fstᵐ
               ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
                         ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
               ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ ⟩ᵐ)
           ∘ᵐ fstᵐ)
        ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
                  ∘ᵐ ⟨ idᵐ ,
                          sndᵐ
                       ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
        ∘ᵐ ⟨ idᵐ ,
                (sndᵐ ∘ᵐ fstᵐ)
             ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ (  (   fstᵐ
           ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
                     ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
           ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ ⟩ᵐ)
       ∘ᵐ fstᵐ)
    ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
              ∘ᵐ ⟨ idᵐ ,
                      sndᵐ
                   ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
    ∘ᵐ ⟨ idᵐ ,
            (sndᵐ ∘ᵐ fstᵐ)
         ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ 
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
      (trans (⟨⟩ᵐ-fstᵐ _ _) (trans (∘ᵐ-identityʳ _) (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ (⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ idᵐ ,
          idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
       ∘ᵐ fstᵐ)
    ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
              ∘ᵐ ⟨ idᵐ ,
                      sndᵐ
                   ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
    ∘ᵐ ⟨ idᵐ ,
            (sndᵐ ∘ᵐ fstᵐ)
         ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ 
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ idᵐ ,
          idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ fstᵐ
    ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
              ∘ᵐ ⟨ idᵐ ,
                      sndᵐ
                   ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
    ∘ᵐ ⟨ idᵐ ,
            (sndᵐ ∘ᵐ fstᵐ)
         ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ 
    ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
      (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ idᵐ ,
              idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ fstᵐ
        ∘ᵐ mapˣᵐ (   mapˣᵐ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) idᵐ
                  ∘ᵐ ⟨ idᵐ ,
                          sndᵐ
                       ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ) idᵐ
        ∘ᵐ ⟨ idᵐ ,
                (sndᵐ ∘ᵐ fstᵐ)
             ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ (⟦ Γ ⟧ᵉᶠ terminalᵐ) idᵐ) idᵐ) idᵐ ⟩ᵐ 
        ∘ᵐ ⟨ idᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))))
      (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))))
        (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
          (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))) (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
            (trans (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _))) (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))))
              (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (trans
                (cong₂ ⟨_,_⟩ᵐ
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                    (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                      (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
                        (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                          (trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
                            (trans (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                              (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-assoc _ _ _)
                                (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _))))))))))))
                  (trans (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (⟨⟩ᵐ-sndᵐ _ _)))
                    (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                      (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
                        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                          (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                            (cong₂ ⟨_,_⟩ᵐ
                              (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _)))
                              (⟨⟩ᵐ-sndᵐ _ _)))))))))))))
              (sym (⟨⟩ᵐ-unique _ _ _
                (∘ᵐ-identityʳ _)
                (trans (∘ᵐ-identityʳ _)
                  (⟨⟩ᵐ-unique _ _ _ refl refl))))))))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ sym (C-subst≡∘ᵐ M Hd V) ⟩
    ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ
  ∎
