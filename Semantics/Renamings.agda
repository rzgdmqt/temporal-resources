-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Semantics.Model

module Semantics.Renamings (Mod : Model) where

open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod

open import Util.Equality
open import Util.Time

open Model Mod

-- Semantics of renamings as maps between environments

⟦_⟧ʳ : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → {A : Obj} → ⟦ Γ' ⟧ᵉᵒ A →ᵐ ⟦ Γ ⟧ᵉᵒ A
⟦ id-ren ⟧ʳ =
  idᵐ
⟦ ρ' ∘ʳ ρ ⟧ʳ =
  ⟦ ρ ⟧ʳ ∘ᵐ ⟦ ρ' ⟧ʳ
⟦ wk-ren ⟧ʳ =
  fstᵐ
⟦ var-ren {Γ = Γ} x ⟧ʳ =
  ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ ⟧ᵉᶠ terminalᵐ ⟩ᵐ
⟦ ⟨⟩-η-ren ⟧ʳ =
  η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ =
  η⁻¹
⟦ ⟨⟩-μ-ren {Γ} {τ} {τ'} ⟧ʳ {A} =
  ⟨⟩-≤ (≤-reflexive (+-comm τ τ')) ∘ᵐ μ {⟦ Γ ⟧ᵉᵒ A}
⟦ ⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} ⟧ʳ {A} =
  μ⁻¹ {⟦ Γ ⟧ᵉᵒ A} ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
⟦ ⟨⟩-≤-ren p ⟧ʳ =
  ⟨⟩-≤ p
⟦ cong-∷-ren ρ ⟧ʳ =
  mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
⟦ cong-⟨⟩-ren {τ = τ} ρ ⟧ʳ =
  ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ


-- Semantics of renamings is natural

⟦⟧ʳ-nat : ∀ {Γ Γ' A B}
        → (ρ : Ren Γ Γ')
        → (f : A →ᵐ B)
        → ⟦ Γ ⟧ᵉᶠ f ∘ᵐ ⟦ ρ ⟧ʳ
        ≡ ⟦ ρ ⟧ʳ ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f
        
⟦⟧ʳ-nat {Γ} {.Γ} {A} {B} id-ren f = 
  begin
    ⟦ Γ ⟧ᵉᶠ f ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    ⟦ Γ ⟧ᵉᶠ f
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
    idᵐ ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
  ∎
⟦⟧ʳ-nat {Γ} {Γ'} {A} {B} (_∘ʳ_ {Γ' = Γ''} ρ ρ') f = 
  begin
    ⟦ Γ ⟧ᵉᶠ f ∘ᵐ ⟦ ρ' ⟧ʳ ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (⟦ Γ ⟧ᵉᶠ f ∘ᵐ ⟦ ρ' ⟧ʳ) ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congˡ (⟦⟧ʳ-nat ρ' f) ⟩
    (⟦ ρ' ⟧ʳ ∘ᵐ ⟦ Γ'' ⟧ᵉᶠ f) ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
    ⟦ ρ' ⟧ʳ ∘ᵐ ⟦ Γ'' ⟧ᵉᶠ f ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-congʳ (⟦⟧ʳ-nat ρ f) ⟩
    ⟦ ρ' ⟧ʳ ∘ᵐ ⟦ ρ ⟧ʳ ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
    (⟦ ρ' ⟧ʳ ∘ᵐ ⟦ ρ ⟧ʳ) ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f
  ∎
⟦⟧ʳ-nat {Γ} {.(Γ ∷ _)} {A} {B} wk-ren f = 
  begin
    ⟦ Γ ⟧ᵉᶠ f ∘ᵐ fstᵐ
  ≡⟨ sym (⟨⟩ᵐ-fstᵐ _ _) ⟩
    fstᵐ ∘ᵐ ⟨ ⟦ Γ ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ∎
⟦⟧ʳ-nat {.(Γ' ∷ _)} {Γ'} {A} {B} (var-ren x) f = 
  begin
       ⟨ ⟦ Γ' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ' ⟧ᵉᶠ terminalᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
      ⟨ (⟦ Γ' ⟧ᵉᶠ f ∘ᵐ fstᵐ) ∘ᵐ ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ' ⟧ᵉᶠ terminalᵐ ⟩ᵐ ,
         (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ' ⟧ᵉᶠ terminalᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
       (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
         (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))))
       (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
         (trans (∘ᵐ-identityˡ _)
           (trans (∘ᵐ-congʳ (trans
             (cong ⟦ Γ' ⟧ᵉᶠ (sym terminalᵐ-unique))
               (⟦⟧ᵉ-∘ᵐ {Γ'} _ _))) (sym (∘ᵐ-assoc _ _ _)))))) ⟩
      ⟨ idᵐ ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f ,
        (var-in-env x ∘ᵐ ⟦ Γ' ⟧ᵉᶠ terminalᵐ) ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       ⟨ idᵐ , var-in-env x ∘ᵐ ⟦ Γ' ⟧ᵉᶠ terminalᵐ ⟩ᵐ
    ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f
  ∎
⟦⟧ʳ-nat {.(Γ' ⟨ 0 ⟩)} {Γ'} {A} {B} ⟨⟩-η-ren f = 
  begin
    ⟨ 0 ⟩ᶠ (⟦ Γ' ⟧ᵉᶠ f) ∘ᵐ η
  ≡⟨ ⟨⟩-η-nat _ ⟩
    η ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f
  ∎
⟦⟧ʳ-nat {Γ} {.(Γ ⟨ 0 ⟩)} {A} {B} ⟨⟩-η⁻¹-ren f = 
  begin
    ⟦ Γ ⟧ᵉᶠ f ∘ᵐ η⁻¹
  ≡⟨ ⟨⟩-η⁻¹-nat _ ⟩
    η⁻¹ ∘ᵐ ⟨ 0 ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ∎
⟦⟧ʳ-nat {_} {Γ ⟨ τ ⟩ ⟨ τ' ⟩} {A} {B} ⟨⟩-μ-ren f = 
  begin
       ⟨ τ + τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ τ'))
    ∘ᵐ μ
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨ τ + τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ τ')))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-≤-nat _ _) ⟩
       (   ⟨⟩-≤ (≤-reflexive (+-comm τ τ'))
        ∘ᵐ ⟨ τ' + τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm τ τ'))
    ∘ᵐ ⟨ τ' + τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ μ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-μ-nat _) ⟩
       ⟨⟩-≤ (≤-reflexive (+-comm τ τ'))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨⟩-≤ (≤-reflexive (+-comm τ τ'))
        ∘ᵐ μ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
  ∎
⟦⟧ʳ-nat {Γ ⟨ τ ⟩ ⟨ τ' ⟩} {_} {A} {B} ⟨⟩-μ⁻¹-ren f = 
  begin
       ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   ⟨ τ' ⟩ᶠ (⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-μ⁻¹-nat _) ⟩
       (   μ⁻¹
        ∘ᵐ ⟨ τ' + τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨ τ' + τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-≤-nat _ _) ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ))
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (+-comm τ' τ)))
    ∘ᵐ ⟨ τ + τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ∎
⟦⟧ʳ-nat {Γ ⟨ τ ⟩} {_ ⟨ τ' ⟩} {A} {B} (⟨⟩-≤-ren p) f = 
  begin
       ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ ⟨⟩-≤ p
  ≡⟨ ⟨⟩-≤-nat _ _ ⟩
       ⟨⟩-≤ p
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ∎
⟦⟧ʳ-nat {Γ ∷ C} {Γ' ∷ _} {A} {B} (cong-∷-ren ρ) f = 
  begin
       mapˣᵐ (⟦ Γ ⟧ᵉᶠ f) idᵐ
    ∘ᵐ mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
  ≡⟨ sym (mapˣᵐ-∘ᵐ _ _ _ _) ⟩
       mapˣᵐ (⟦ Γ ⟧ᵉᶠ f ∘ᵐ ⟦ ρ ⟧ʳ) (idᵐ ∘ᵐ idᵐ)
  ≡⟨ cong (λ g → mapˣᵐ g (idᵐ ∘ᵐ idᵐ)) (⟦⟧ʳ-nat ρ f) ⟩
       mapˣᵐ (⟦ ρ ⟧ʳ ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f) (idᵐ ∘ᵐ idᵐ)
  ≡⟨ mapˣᵐ-∘ᵐ _ _ _ _ ⟩
       mapˣᵐ ⟦ ρ ⟧ʳ idᵐ
    ∘ᵐ mapˣᵐ (⟦ Γ' ⟧ᵉᶠ f) idᵐ
  ∎
⟦⟧ʳ-nat {Γ ⟨ τ ⟩} {Γ' ⟨ τ ⟩} {A} {B} (cong-⟨⟩-ren ρ) f = 
  begin
       ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
  ≡⟨ sym (⟨⟩-∘ᵐ _ _) ⟩
    ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f ∘ᵐ ⟦ ρ ⟧ʳ)
  ≡⟨ cong ⟨ τ ⟩ᶠ (⟦⟧ʳ-nat ρ f) ⟩
    ⟨ τ ⟩ᶠ (⟦ ρ ⟧ʳ ∘ᵐ ⟦ Γ' ⟧ᵉᶠ f)
  ≡⟨ ⟨⟩-∘ᵐ _ _ ⟩
       ⟨ τ ⟩ᶠ ⟦ ρ ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (⟦ Γ' ⟧ᵉᶠ f)
  ∎
