{-# OPTIONS --allow-unsolved-metas #-}

-- Due to the eta-contraction bug noted below

----------------------------------------------------------------------------------
-- Interaction of the auxiliary lemma for the semantics of unbox and weakenings --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.var-not-in-ctx-after-ᶜ-wk-ren (Mod : Model) where

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts
open import Syntax.Renamings
open import Syntax.Substitutions

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Util.Equality
open import Util.Time

open Model Mod

var-not-in-ctx-after-ᶜ-wk-ren : ∀ {Γ A B τ τ'}
                                → (p : τ' > τ)
                                → (x : A ∈[ τ ] Γ)
                                →    ⟦ eq-ren (var-not-in-ctx-after-ᶜ x p) ⟧ʳ
                                  ∘ᵐ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} (wk-ren {A = A}) -ʳ τ' ⟧ʳ {B}
                                ≡ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ

var-not-in-ctx-after-ᶜ-wk-ren {.(_ ∷ A)} {A} {B} {.0} {suc τ'} p Hd = 
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
var-not-in-ctx-after-ᶜ-wk-ren {.(_ ∷ _)} {A} {B} {τ} {suc τ'} p (Tl-∷ {B = C} x) = 
  begin
       ⟦ eq-ren (var-not-in-ctx-after-ᶜ x p) ⟧ʳ
    ∘ᵐ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} wk-ren -ʳ suc τ' ⟧ʳ
  ≡⟨ var-not-in-ctx-after-ᶜ-wk-ren p x ⟩
      ⟦ eq-ren (cong (_-ᶜ suc τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
  ≡⟨ cong (λ p → ⟦ eq-ren p ⟧ʳ)
       {cong (_-ᶜ suc τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))}
       {cong (_-ᶜ suc τ') (sym (cong (_∷ C) (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))}
       uip ⟩
      ⟦ eq-ren (cong (_-ᶜ suc τ') (sym (cong (_∷ C) (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))) ⟧ʳ
  ∎
var-not-in-ctx-after-ᶜ-wk-ren {Γ ⟨ τ ⟩} {A} {B} {_} {suc τ'} (s≤s p) (Tl-⟨⟩ {τ' = τ''} x) =
  {!!}

  where

  -- TODO: Proving the two cases separately due to `with` throwing an error, related to #2732 about eta-contraction not being type-preserving

  var-not-in-ctx-after-ᶜ-wk-ren-Tl-yes : (q : suc τ' ≤ τ)
                                       →  ⊥-elim (sucn≤m⇒m+k≤n-contradiction q p)
                                       ∘ᵐ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} (wk-ren {A = A}) ⟧ʳ
                                       ≡ ⟦ eq-ren (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))) ⟧ʳ {B}
  var-not-in-ctx-after-ᶜ-wk-ren-Tl-yes q =
    ⊥-elim (sucn≤m⇒m+k≤n-contradiction q p)

  var-not-in-ctx-after-ᶜ-wk-ren-Tl-no : (q : ¬ (suc τ' ≤ τ))
                                      →    ⟦ eq-ren (var-not-in-ctx-after-ᶜ {Γ} {τ' = suc τ' ∸ τ} x (
                                                      (≤-trans
                                                        (≤-trans
                                                          (+-monoʳ-≤ 1 (≤-reflexive (sym (m+n∸m≡n τ τ''))))
                                                          (≤-reflexive (sym (+-∸-assoc 1 {τ + τ''} {τ} (≤-stepsʳ τ'' ≤-refl)))))
                                                        (∸-monoˡ-≤ τ (+-monoʳ-≤ 1 p))))) ⟧ʳ
                                        ∘ᵐ ⟦ (cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} (wk-ren {A = A})) -ʳ (suc τ' ∸ τ) ⟧ʳ
                                      ≡ ⟦ eq-ren (cong (_-ᶜ (suc τ' ∸ τ)) (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ {B}                            
  var-not-in-ctx-after-ᶜ-wk-ren-Tl-no q = 
    begin
         ⟦ eq-ren (var-not-in-ctx-after-ᶜ {Γ} {τ' = suc τ' ∸ τ} x (
                               (≤-trans
                      (≤-trans
                        (+-monoʳ-≤ 1 (≤-reflexive (sym (m+n∸m≡n τ τ''))))
                        (≤-reflexive (sym (+-∸-assoc 1 {τ + τ''} {τ} (≤-stepsʳ τ'' ≤-refl)))))
                      (∸-monoˡ-≤ τ (+-monoʳ-≤ 1 p))))) ⟧ʳ {B}
      ∘ᵐ ⟦ (cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} (wk-ren {A = A})) -ʳ (suc τ' ∸ τ) ⟧ʳ
    ≡⟨ var-not-in-ctx-after-ᶜ-wk-ren _ x ⟩
      ⟦ eq-ren (cong (_-ᶜ (suc τ' ∸ τ)) (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ
    ∎
