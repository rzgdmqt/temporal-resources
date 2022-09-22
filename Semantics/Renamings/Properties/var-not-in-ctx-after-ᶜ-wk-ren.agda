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
open import Semantics.Renamings.Core Mod

open import Util.Equality
open import Util.Time

open Model Mod

postulate
  var-not-in-ctx-after-ᶜ-wk-ren : ∀ {Γ A B τ τ'}
                                → (p : τ' > τ)
                                → (x : A ∈[ τ ] Γ)
                                →    ⟦ eq-ren (var-not-in-ctx-after-ᶜ x p) ⟧ʳ
                                  ∘ᵐ ⟦ cong-ren {Γ'' = proj₁ (proj₂ (var-split x))} (wk-ren {A = A}) -ʳ τ' ⟧ʳ {B}
                                ≡ ⟦ eq-ren (cong (_-ᶜ τ') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))) ⟧ʳ

{-
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
var-not-in-ctx-after-ᶜ-wk-ren {Γ ⟨ τ ⟩} {A} {B} {_} {suc τ'} (s≤s p) (Tl-⟨⟩ {τ' = τ''} x) with suc τ' ≤? τ
... | q = {!!}
-}



-- TODO: why the failure of the with abstraction in the `Tl-⟨⟩ {τ' = τ''} x` case?

{-

τ' <ᵇ τ != does w of type Agda.Builtin.Bool.Bool
when checking that the type
(τ : Time) (τ' : ℕ) (w : Dec (suc τ' ≤ τ)) (Mod : Model) (Γ : Ctx)
{A : Syntax.Types.VType}
{B : Semantics.Model.Category.Category.Obj (Model.Cat Mod)}
{τ' = τ'' : ℕ} (p : τ + τ'' ≤ τ') (x : A ∈[ τ'' ] Γ) →
(Model.Cat Mod Semantics.Model.Category.Category.∘ᵐ
 Semantics.Renamings.Core.⟦ Mod ⟧ʳ
 (eq-ren (var-not-in-ctx-after-ᶜ (Tl-⟨⟩ x) (s≤s p) | w)))
(Semantics.Renamings.Core.⟦ Mod ⟧ʳ
 (cong-⟨⟩-ren (cong-ren wk-ren) -ʳ suc τ' | w))
≡
Semantics.Renamings.Core.⟦ Mod ⟧ʳ
(eq-ren
 (cong (_-ᶜ suc τ')
  (sym
   (cong (_⟨ τ ⟩) (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))))))
of the generated with function is well-formed

-}
