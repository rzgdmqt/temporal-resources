-----------------------------------------------------------------------
-- Relating syntactic substitutions to semantic morphism composition --
-----------------------------------------------------------------------

open import Semantics.Model

module Semantics.Substitutions.Properties.VC-subst-aux (Mod : Model) where

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

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod


-- Auxiliary substitution lemma for the unbox case

C-subst≡∘ᵐ-aux-unbox : ∀ {Γ A τ τ'}
                     → (x : A ∈[ τ ] Γ)
                     → (y : A ∈[ τ ∸ τ' ] Γ -ᶜ τ')
                     → (W : proj₁ (var-split x) ⊢V⦂ A)
                     → (p : τ' ≤ ctx-time Γ)
                     → (q : τ' ≤ τ)
                     → (r : proj₁ (var-split y) ≡ proj₁ (var-split x))
                     → (s : proj₁ (proj₂ (var-split y)) ≡ proj₁ (proj₂ (var-split x)) -ᶜ τ')
                     →    ⟨ τ' ⟩ᶠ (  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                                   ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                                   ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                                   ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                                       ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
                       ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
                     ≡
                          env-⟨⟩-ᶜ τ' p
                       ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
                       ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
                       ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)

C-subst≡∘ᵐ-aux-unbox {Γ} {A} {τ} {τ'} x y W p q r s =
  begin
       ⟨ τ' ⟩ᶠ (  split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y))))
                ∘ᵐ ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ
                ∘ᵐ split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                ∘ᵐ ⟦   eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
                    ∘ʳ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ ∘ᵐ-congˡ (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ
      (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))))) ⟩
       (   ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ V-rename (eq-ren (sym r)) W ⟧ᵛᵗ ⟩ᵐ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ' ⟩ᶠ (cong ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ
      (cong ⟨ idᵐ ,_⟩ᵐ (V-rename≡∘ᵐ (eq-ren (sym r)) W))))) ⟩
       ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ eq-ren (sym r) ⟧ʳ ⟩ᵐ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       (   ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ eq-ren (sym r) ⟧ʳ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ ∘ᵐ-congˡ (
      begin
           ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ eq-ren (sym r) ⟧ʳ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
           ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ eq-ren (sym r) ⟧ʳ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (   split-env {Γ' = proj₁ (var-split y)} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl)
                    ∘ᵐ ⟦ eq-ren (cong₂ _++ᶜ_ r s) ⟧ʳ)
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ (split-env-eq-renˡʳ r s))) ⟩
           ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ eq-ren (sym r) ⟧ʳ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟦ eq-ren r ⟧ʳ
                    ∘ᵐ ⟦ eq-ren s ⟧ʳ
                    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))) ⟩
           ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ∘ᵐ ⟦ eq-ren (sym r) ⟧ʳ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟦ eq-ren r ⟧ʳ)
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren s ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ
            (trans
              (sym (⟨⟩-∘ᵐ _ _))
              (trans
                (cong ⟨ τ' ⟩ᶠ
                  (trans
                    (sym (⟦⟧ᵉ-∘ᵐ {proj₁ (proj₂ (var-split y))} _ _))
                    (trans
                      (cong ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ
                        (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (trans
                          (cong₂ ⟨_,_⟩ᵐ
                            (trans (∘ᵐ-identityˡ _) (trans (sym (∘ᵐ-identityʳ _))
                              (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))))
                            (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (eq-ren-symˡ r))
                              (trans (∘ᵐ-identityʳ _)
                                (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _))))))))
                          (⟨⟩ᵐ-∘ᵐ _ _ _))))
                      (⟦⟧ᵉ-∘ᵐ {proj₁ (proj₂ (var-split y))} _ _))))
                (⟨⟩-∘ᵐ _ _))))
            (∘ᵐ-assoc _ _ _)) ) ⟩
           ⟨ τ' ⟩ᶠ (split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split y)))))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ (mapˣᵐ ⟦ eq-ren r ⟧ʳ idᵐ))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren s ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ trans (∘ᵐ-congˡ (trans (cong ⟨ τ' ⟩ᶠ (split-env⁻¹-eq-ren (proj₁ (proj₂ (proj₂ (var-split y)))))) (⟨⟩-∘ᵐ _ _))) (∘ᵐ-assoc _ _ _) ⟩
           ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split y) ∷ A} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ (mapˣᵐ ⟦ eq-ren r ⟧ʳ idᵐ))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren s ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong ⟨ τ' ⟩ᶠ (cong ⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ
          (sym (⟨⟩ᵐ-unique _ _ _
            (eq-ren-cong-fstᵐ r)
            (trans (eq-ren-cong-sndᵐ r) (sym (∘ᵐ-identityˡ _))))))))) ⟩
           ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split y) ∷ A} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟦ eq-ren (cong (_∷ A) r) ⟧ʳ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren s ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ
          (trans (sym (⟨⟩-∘ᵐ _ _)) (trans (cong ⟨ τ' ⟩ᶠ (split-env⁻¹-eq-renˡ (cong (_∷ A) r))) (⟨⟩-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _))) ⟩
           ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (λ Γ → Γ ++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split y)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren s ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans
          (∘ᵐ-congˡ (trans (sym (⟨⟩-∘ᵐ _ _))
            (trans (cong ⟨ τ' ⟩ᶠ (⟦⟧ʳ-nat (eq-ren s) ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)) (⟨⟩-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _))))) ⟩
           ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split y))} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren s ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (trans (sym (⟨⟩-∘ᵐ _ _))
            (trans (cong ⟨ τ' ⟩ᶠ (split-env⁻¹-eq-renʳ s)) (⟨⟩-∘ᵐ _ _)))) (∘ᵐ-assoc _ _ _)))) ⟩
           ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (λ Γ → Γ ++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (proj₁ (var-split x) ∷ A ++ᶜ_) s) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
           (   ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
            ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (λ Γ → Γ ++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) ⟧ʳ
            ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (proj₁ (var-split x) ∷ A ++ᶜ_) s) ⟧ʳ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congˡ (sym (trans (⟨⟩-∘ᵐ _ _) (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))) ⟩
           ⟨ τ' ⟩ᶠ (   ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))))) ⟧ʳ
                    ∘ᵐ ⟦ eq-ren (cong (λ Γ → Γ ++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) ⟧ʳ
                    ∘ᵐ ⟦ eq-ren (cong (proj₁ (var-split x) ∷ A ++ᶜ_) s) ⟧ʳ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congˡ (cong ⟨ τ' ⟩ᶠ (
          trans
            (∘ᵐ-congʳ (eq-ren-trans (cong (_++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) (cong (proj₁ (var-split x) ∷ A ++ᶜ_) s)))
            (trans
              (eq-ren-trans
                (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y))))))
                (trans (cong (_++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) (cong (proj₁ (var-split x) ∷ A ++ᶜ_) s)))
              (trans
                (cong (λ p → ⟦ eq-ren p ⟧ʳ)
                  {trans
                    (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y))))))
                    (trans (cong (_++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) r)) (cong (proj₁ (var-split x) ∷ A ++ᶜ_) s))}
                  {trans
                    (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))
                    (sym (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))))}
                  uip)
                (sym (eq-ren-trans
                       (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))
                       (sym (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))))))))) ⟩
           ⟨ τ' ⟩ᶠ (    ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
                    ∘ᵐ  ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                                        (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _) ⟩
           (   ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
            ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                                       (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                                   (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
      ∎) ⟩
       (   ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                                   (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl)))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                               (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong (env-⟨⟩-ᶜ τ') (≤-irrelevant _ _))))))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                               (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {proj₁ (var-split x)} {proj₁ (proj₂ (var-split x))} {τ'}
                          (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x))} τ'
         (≤-trans
           (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))
           (≤-trans
             (m≤n+m (ctx-time (proj₁ (proj₂ (var-split x)))) (ctx-time (proj₁ (var-split x))))
             (≤-reflexive (sym (ctx-time-++ᶜ (proj₁ (var-split x)) (proj₁ (proj₂ (var-split x))))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym
      (env-⟨⟩-ᶜ-split-env-nat τ' (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))))))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                               (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ proj₁ (proj₂ (var-split x)) -ᶜ τ' ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ)
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (env-⟨⟩-ᶜ-nat _ _ _))) (∘ᵐ-assoc _ _ _))))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                               (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ (   ⟨ τ' ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {proj₁ (var-split x) ∷ A} {proj₁ (proj₂ (var-split x))} {τ'}
                                   (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))) ⟧ʳ
        ∘ᵐ ⟨ τ' ⟩ᶠ (split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x)) -ᶜ τ'} (≡-split refl))
        ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (env-⟨⟩-ᶜ-split-env⁻¹-nat τ' (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ (   env-⟨⟩-ᶜ τ'
             (≤-trans
              (≤-trans q (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x)))))))
              (≤-trans
               (m≤n+m (ctx-time (proj₁ (proj₂ (var-split x)))) (ctx-time (proj₁ (var-split x))))
               (≤-reflexive (sym (ctx-time-++ᶜ (proj₁ (var-split x) ∷ A) (proj₁ (proj₂ (var-split x))))))))
        ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-congˡ (cong (env-⟨⟩-ᶜ τ') (≤-irrelevant _ _)))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ (   env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (sym (cong ctx-time (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
        ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (sym (cong ctx-time (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
    ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong (env-⟨⟩-ᶜ τ') (≤-irrelevant _ _))) ⟩
       ⟨ τ' ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ τ' (≤-trans p (≤-reflexive (cong ctx-time (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
    ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ trans
      (sym (∘ᵐ-assoc _ _ _))
      (trans
        (∘ᵐ-congˡ (sym (env-⟨⟩-ᶜ-eq-ren-nat τ' p (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
        (∘ᵐ-assoc _ _ _)) ⟩
       env-⟨⟩-ᶜ τ' p
    ∘ᵐ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))) ⟧ʳ
    ∘ᵐ split-env⁻¹ {Γ' = proj₁ (var-split x) ∷ A} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ
      (trans
        (sym (∘ᵐ-assoc _ _ _))
        (∘ᵐ-congˡ (sym (split-env⁻¹-eq-ren (proj₁ (proj₂ (proj₂ (var-split x)))))))) ⟩
       env-⟨⟩-ᶜ τ' p
    ∘ᵐ split-env⁻¹ (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ ⟦ proj₁ (proj₂ (var-split x)) ⟧ᵉᶠ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ split-env {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split x))} (≡-split refl)
  ∎
