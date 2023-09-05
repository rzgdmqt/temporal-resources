{-# OPTIONS --allow-unsolved-metas #-}
module EquationalTheory.Soundness where

open import OperationalSemantics.PerservationTheorem
open import OperationalSemantics.ProgressTheorem
open import OperationalSemantics.State

open import EquationalTheory.CompContext
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

-- Propositional equality implies equality in equational theory

≡-to-== : ∀ {Γ A τ}
        → {M N : Γ ⊢C⦂ A ‼ τ}
        → (M ≡ N)
        --------------------
        → Γ ⊢C⦂ M == N
≡-to-== refl = C-refl

-- Congruence rule for τ-subst (with respect to the equational theory)

τ-subst-cong : ∀ {Γ A τ τ'}
             → {M M' : Γ ⊢C⦂ A ‼ τ}
             → (p : τ ≡ τ')
             → (q : τ ≡ τ')
             → (Γ ⊢C⦂ M == M')
             ----------------------------------
             → Γ ⊢C⦂ τ-subst p M == τ-subst q M'
τ-subst-cong refl refl r = r

-- Computation contexts corresponding to states

data _⊢SK[_] (Γ : Ctx) : BCtx → Set where

    []ₛₖ    : 
            --------------
              Γ ⊢SK[ []ₗ ]

    boxₛₖ   : ∀ {Δ A τ}
            → Γ ⟨ τ ⟩ ⊢V⦂ A
            → Γ ∷ [ τ ] A ⊢SK[ Δ ]
            -----------------------
            → Γ ⊢SK[ [ τ ] A ∷ₗ Δ ]

    delayₛₖ : ∀ {Δ}
            → (τ : Time)
            → Γ ⟨ τ ⟩ ⊢SK[ Δ ]
            -------------------
            → Γ ⊢SK[ ⟨ τ ⟩ₗ Δ ]

-- Translating a state into a corresponding computation context

toStateCtxAcc : ∀ {Δ Δ' τ}
              → (S : 𝕊 τ)
              → (K : toCtx S ⊢SK[ Δ ])
              → Δ' ≡ Ctx→Bctx (toCtx S) ++ₗ Δ
              → [] ⊢SK[ Δ' ]

toStateCtxAcc {Δ} {.(Ctx→Bctx (toCtx ∅) ++ₗ Δ)} {.0} ∅ K refl =
  K
toStateCtxAcc {Δ} {Δ'} {.(_ + τ')} (S ⟨ τ' ⟩ₘ) K p =
  toStateCtxAcc S
    (delayₛₖ τ' K)
    (trans p ((++ₗ-assoc (Ctx→Bctx (toCtx S)) (⟨ τ' ⟩ₗ []ₗ) Δ)))
toStateCtxAcc {Δ} {Δ'} {τ} (S ∷ₘ[ τ' ] V) K p =
  toStateCtxAcc S
    (boxₛₖ V K)
    (trans p (++ₗ-assoc (Ctx→Bctx (toCtx S)) ([ τ' ] _ ∷ₗ []ₗ) Δ)) 

toStateCtx : ∀ {τ} 
           → (S : 𝕊 τ)
           → [] ⊢SK[ Ctx→Bctx (toCtx S)]

toStateCtx S =
  toStateCtxAcc S []ₛₖ (sym (++ₗ-identityʳ))


-- Filling a hole in a computation context corresponding to a state

_[_]ₛₖ : ∀ {Γ Δ A τ} 
       → (K : Γ ⊢SK[ Δ ])
       → (M : Γ ⋈ Δ ⊢C⦂ A ‼ τ)
       → Γ ⊢C⦂ A ‼ (bctx-time Δ + τ)

_[_]ₛₖ {Γ} {.[]ₗ} {A} {τ} []ₛₖ M =
  M
_[_]ₛₖ {Γ} {.([ _ ] _ ∷ₗ _)} {A} {τ} (boxₛₖ V K) M =
  box V (K [ M ]ₛₖ)
_[_]ₛₖ {Γ} {.(⟨ τ' ⟩ₗ _)} {A} {τ} (delayₛₖ {Δ = Δ} τ' K) M =
  τ-subst (sym (+-assoc τ' (bctx-time Δ) τ)) (delay τ' (K [ M ]ₛₖ))

{-
_[_∣_]ₛₖ : ∀ {Γ Γ' Δ A τ} 
       → (K : Γ ⊢SK[ Δ ])
       → Γ' ≡ Γ ⋈ Δ
       → (M : Γ' ⊢C⦂ A ‼ τ)
       → Γ ⊢C⦂ A ‼ (bctx-time Δ + τ)

_[_∣_]ₛₖ {Γ} {.(Γ ⋈ []ₗ)} {.[]ₗ} {A} {τ} []ₛₖ refl M =
  M
_[_∣_]ₛₖ {Γ} {Γ'} {.([ _ ] _ ∷ₗ _)} {A} {τ} (boxₛₖ V K) p M =
  box V (K [ p ∣ M ]ₛₖ)
_[_∣_]ₛₖ {Γ} {Γ'} {.(⟨ τ' ⟩ₗ _)} {A} {τ} (delayₛₖ {Δ = Δ} τ' K) p M =
  τ-subst (sym (+-assoc τ' (bctx-time Δ) τ)) (delay τ' (K [ p ∣ M ]ₛₖ))

_[_]ₛₖ : ∀ {A τ τ'} {S : 𝕊 τ} 
       → (K : [] ⊢SK[ Ctx→Bctx (toCtx S)])
       → (M : toCtx S ⊢C⦂ A ‼ τ')
       → [] ⊢C⦂ A ‼ (bctx-time (Ctx→Bctx (toCtx S)) + τ')

_[_]ₛₖ {A} {τ} {τ'} {S} K M =
  K [ sym (trans (⋈-BCtx→Ctx [] (toCtx S)) ++ᶜ-identityˡ) ∣ M ]ₛₖ
-}


-- Congruence rule for computation context hole filling (with respect to the equational theory)


stateCtx-cong : ∀ {Γ Δ A τ}
              → (K : Γ ⊢SK[ Δ ])
              → {M N : Γ ⋈ Δ ⊢C⦂ A ‼ τ}
              → Γ ⋈ Δ ⊢C⦂ M == N
              → Γ ⊢C⦂ K [ M ]ₛₖ == K [ N ]ₛₖ

stateCtx-cong {Γ} {.[]ₗ} {A} {τ} []ₛₖ M==N =
  M==N
stateCtx-cong {Γ} {.([ _ ] _ ∷ₗ _)} {A} {τ} (boxₛₖ V K) M==N =
  box-cong V-refl (stateCtx-cong K M==N)
stateCtx-cong {Γ} {.(⟨ τ' ⟩ₗ _)} {A} {τ} (delayₛₖ {Δ = Δ} τ' K) M==N =
  τ-subst-cong
    (sym (+-assoc τ' (bctx-time Δ) τ))
    (sym (+-assoc τ' (bctx-time Δ) τ))
    (delay-cong (stateCtx-cong K M==N))

-- Algebraicity of computation contexts

[]ₛₖ-algebraicity : ∀ {Γ Δ A B τ τ'}
                  → (K : Γ ⊢SK[ Δ ])
                  → (M : Γ ⋈ Δ ⊢C⦂ A ‼ τ)
                  → (N : Γ ⟨ bctx-time Δ + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                  → Γ ⊢C⦂ ((K [ M ]ₛₖ) ; N)
                      == τ-subst
                           (sym (+-assoc (bctx-time Δ) τ τ' ))
                             (K [ M ;
                                  C-rename
                                    (   {!!}
                                     ∘ʳ cong-∷-ren (⟨⟩-μ-ren {τ = bctx-time Δ} {τ' = τ}))
                                    N ]ₛₖ)

[]ₛₖ-algebraicity = {!!}


-- Soundness theorem

{-
soundness : ∀ {A τ τ' τ'' τ'''}
        → {S : 𝕊 τ} 
        → {S' : 𝕊 τ'}
        → {M : toCtx S ⊢C⦂ A ‼ τ''}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
        → (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩)
        → let p = trans (cong (_+ τ''') (trans (bctx-time-ctx-time (toCtx S')) (ctx-timeSτ≡τ S')))
                    (trans
                      (sym (proj₂ (perservation-theorem M↝M')))
                      (cong (_+ τ'') (sym (trans (bctx-time-ctx-time (toCtx S)) (ctx-timeSτ≡τ S))))) in
                      
          [] ⊢C⦂ (toStateCtx S) [ M ]ₛₖ
             == τ-subst p ((toStateCtx S') [ M' ]ₛₖ)

soundness {τ''' = τ'''} {S = S} APP =
  C-trans
    (stateCtx-cong
      (toStateCtx S)
      (sym (trans (⋈-BCtx→Ctx [] (toCtx S)) ++ᶜ-identityˡ))
      (fun-beta _ _))
    (τ-subst-cong
      refl
      (trans
        (cong (_+ τ''')
          (trans (bctx-time-ctx-time (toCtx S)) (ctx-timeSτ≡τ S)))
        (cong (_+ τ''')
          (sym (trans (bctx-time-ctx-time (toCtx S)) (ctx-timeSτ≡τ S)))))
      C-refl)
soundness {τ''' = τ'''} {S = S} MATCH =
  C-trans
    (stateCtx-cong
      (toStateCtx S)
      (sym (trans (⋈-BCtx→Ctx [] (toCtx S)) ++ᶜ-identityˡ))
      (match-beta _ _ _))
    (τ-subst-cong
      refl
      (trans
        (cong (_+ τ''')
         (trans (bctx-time-ctx-time (toCtx S)) (ctx-timeSτ≡τ S)))
        (cong (_+ τ''')
         (sym (trans (bctx-time-ctx-time (toCtx S)) (ctx-timeSτ≡τ S)))))
      C-refl)
soundness (SEQ-FST τ+τ₂≡τ₁+τ₄ M↝M') = {!!}
soundness SEQ-RET = {!!}
soundness SEQ-OP = {!!}
soundness DELAY = {!!}
soundness HANDLE-RET = {!!}
soundness (HANDLE-STEP τ+τ₂≡τ₄+τ₃ M↝M') = {!!}
soundness HANDLE-OP = {!!}
soundness BOX = {!!}
soundness (UNBOX p) = {!!}
-}

