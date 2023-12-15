module SoundnessAdequacity.Soundness where

open import SoundnessAdequacity.StateCompContext
open import Syntax.CompContext

open import OperationalSemantics.State
open import OperationalSemantics.ProgressTheorem
open import OperationalSemantics.PerservationTheorem

open import EquationalTheory.EquationalTheory

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.Types

open import Util.Equality
open import Data.Empty
open import Util.Operations
open import Data.Product
open import Util.Time

{-
-- Compatibility relation between evaluation contexts

data _~[_]~_ : ∀ {Γ Γ' CH CH' C C'} → Γ ⊢K[ eval ◁ CH ]⦂ C → Ren Γ Γ' → Γ' ⊢K[ eval ◁ CH' ]⦂ C' → Set where

  ~[]ₖ : ∀ {Γ Γ' CH CH' ρ}
       → []ₖ {Γ} {eval} {CH} ~[ ρ ]~ []ₖ {Γ'} {eval} {CH'}

  ~let : ∀ {Γ Γ' CH CH' A B C τ τ' τ''}
       → {E : Γ ⊢K[ eval ◁ CH ]⦂ (A ‼ τ)}
       → {E' : Γ' ⊢K[ eval ◁ CH' ]⦂ (B ‼ τ')}
       → {N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ C ‼ τ''}
       → {ρ : Ren Γ Γ'}
       → E ~[ ρ ]~ E'
       → (E ₖ[ f≤ᶠf ]; N) ~[ ρ ]~ (E' ₖ[ f≤ᶠf ]; C-rename {!!} N)
-}


-- Soundness theorem

soundness : ∀ {A B τ₁ τ₂ τ₃}
        → {S S' : 𝕊 []} 
        → {M : toCtx S ⊢C⦂ A ‼ τ₁}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ₂}
        → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → (E : hole-ctx (toK S) ⊢K[ eval ◁ A ‼ τ₁ ]⦂ B ‼ (τ₁ + τ₃))
        → (E' : hole-ctx (toK S') ⊢K[ eval ◁ A ‼ τ₂ ]⦂ B ‼ (τ₂ + τ₃))
        → {!!} -- TODO: this variant would ne some kind of compatibility relation between E and E' (that modulo weakening renamings they have the same structure)
        → let ρ = eq-ren
                    (trans
                      (sym ++ᶜ-identityˡ)
                      (trans
                        (toCtx-rel-hole-ctx S)
                        (cong (rel-hole-ctx (toK S) [] ++ᶜ_) (sym (eval-hole-ctx E)))))
                     in
          let ρ' = eq-ren
                     (trans
                       (sym ++ᶜ-identityˡ)
                       (trans
                         (toCtx-rel-hole-ctx S')
                         (cong (rel-hole-ctx (toK S') [] ++ᶜ_) (sym (eval-hole-ctx E')))))
                     in
          [] ⊢C⦂
             toK S [ C-rename (eq-ren (sym ++ᶜ-identityˡ)) (E [ C-rename ρ M ]) ]
             ==
             toK S' [ C-rename (eq-ren (sym ++ᶜ-identityˡ)) (E' [ C-rename ρ' M' ]) ]

soundness M↝M' E = {!!}

