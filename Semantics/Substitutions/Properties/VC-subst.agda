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
open import Semantics.Renamings.Properties.split-env-eq-ren Mod

open import Semantics.Substitutions.Properties.var-subst Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

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
  ≡⟨ {!!} ⟩
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
  ≡⟨ {!!} ⟩
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




{-

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
    {!!}
  {-
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
  -}

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
    {!!}
  {-
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
  -}
  C-subst≡∘ᵐ (V · V') x W =
    {!!}
  {-
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
  -}
  C-subst≡∘ᵐ (absurd V) x W =
    {!!}
  {-
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
  -}
  C-subst≡∘ᵐ (perform op V M) x W =
    {!!}
  {-
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
  -}
  C-subst≡∘ᵐ (handle M `with H `in N) x W =
    {!!}
  {-
    begin
         uncurryᵐ (   T-alg-of-handlerᵀ
                   ∘ᵐ ⟨ (λ op →
                          ⟨ (λ τ'' →
                              (   curryᵐ (   idᵐ
                                          ∘ᵐ uncurryᵐ idᵐ
                                          ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ ,
                                                 ⟨    ⟦⟧ᵍ-⟦⟧ᵛ (param op)
                                                   ∘ᵐ fstᵐ ,
                                                      [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                                                   ∘ᵐ sndᵐ ⟩ᵐ
                                              ∘ᵐ sndᵐ ⟩ᵐ)
                               ∘ᵐ curryᵐ (   ⟦ H op τ'' [ Tl-∷ (Tl-∷ x) ↦ W ]c ⟧ᶜᵗ
                                          ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                           ∘ᵐ projᵐ τ'') ⟩ᵢᵐ
                       ∘ᵐ projᵐ op) ⟩ᵢᵐ
                   ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ
    ≡⟨ {!!} ⟩
         (  uncurryᵐ (   T-alg-of-handlerᵀ
                      ∘ᵐ ⟨ (λ op →
                             ⟨ (λ τ'' →
                                    (  curryᵐ (   idᵐ
                                               ∘ᵐ uncurryᵐ idᵐ
                                               ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ
                                               ,
                                                  ⟨   ⟦⟧ᵍ-⟦⟧ᵛ (param op)
                                                   ∘ᵐ fstᵐ
                                                   ,
                                                      [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵛ-⟦⟧ᵍ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                                                   ∘ᵐ sndᵐ ⟩ᵐ
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
  -}
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
        ≡⟨ {!!} ⟩
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
  C-subst≡∘ᵐ {τ = τ} (unbox {τ = τ'} p V M) x W | no ¬q = {!!}
  C-subst≡∘ᵐ (delay τ M) x W =
    {!!}
  {-
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
  -}


-}
