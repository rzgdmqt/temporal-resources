{-# OPTIONS --allow-unsolved-metas #-}
module OperationalSemantics.Soundness where

open import Syntax.EquationalTheory
open import OperationalSemantics.PerservationTheorem
open import OperationalSemantics.ProgressTheorem
open import Syntax.CompContext
open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import OperationalSemantics.State
open import Syntax.Renamings
open import Syntax.Substitutions

open import Util.Equality
open import Util.Time
open import Util.Properties
open import Util.Operations
open import Data.Empty
open import Data.Product

eq-subst : ∀ {Γ A τ}
        → {M N : Γ ⊢C⦂ A ‼ τ}
        → (M ≡ N)
        ---------------
        → Γ ⊢C⦂ M == N
eq-subst refl = C-refl

double-τ-subst : ∀ {Γ A τ τ'}
        → {M M' : Γ ⊢C⦂ A ‼ τ}
        → (p : τ ≡ τ')
        → (Γ ⊢C⦂ M == M')
        ----------------------------------
        → Γ ⊢C⦂ τ-subst p M == τ-subst p M'
double-τ-subst refl M==M' = M==M'

τ-subst-trans : ∀ {Γ A}
        → {τ τ' τ'' : Time}
        → (p : τ ≡ τ')
        → (q : τ' ≡ τ'')
        → (M : Γ ⊢C⦂ A ‼ τ)
        → τ-subst (trans p q) M ≡ τ-subst q (τ-subst p M)
τ-subst-trans refl refl M = refl

config-to-comp : ∀ {A τ τ'} 
        → (S : 𝕊 τ)
        → (M : toCtx S ⊢C⦂ A ‼ τ')
        → [] ⊢C⦂ A ‼ (τ + τ')
config-to-comp {τ = .0} ∅ M = M
config-to-comp {τ = .(τ' + τ'')} {τ'''} (_⟨_⟩ₘ {τ'} S τ'') M = 
    τ-subst (sym (+-assoc τ' τ'' τ''')) (config-to-comp S (delay τ'' M))
config-to-comp {τ = τ} (S ∷ₘ[ τ' ] V) M = config-to-comp S (box V M)


-- lemma about passing equation under the config-to-comp

M==N⇒confM==confN : ∀ {A τ τ'}
        → {S : 𝕊 τ}
        → {M M' : toCtx S ⊢C⦂ A ‼ τ'}
        → toCtx S ⊢C⦂ M == M'
        → [] ⊢C⦂ 
            config-to-comp S M 
            == 
            config-to-comp S M' 
M==N⇒confM==confN {τ = .0} {τ'} {S = ∅} {M = M} {M' = M'} M==M' = 
    M==M'
M==N⇒confM==confN {τ = .(τ''' + τ'')} {τ'} {S = _⟨_⟩ₘ {τ'''} S τ''} {M = M} {M' = M'} M==M' = 
    double-τ-subst (sym (+-assoc τ''' τ'' τ')) (M==N⇒confM==confN (delay-cong M==M'))
M==N⇒confM==confN {τ = τ} {S = S ∷ₘ[ τ' ] x} {M = M} {M' = M'} M==M' = 
    M==N⇒confM==confN (box-cong V-refl M==M') 


-----------------------
-- Soundness theorem --
-----------------------

remove-subst : ∀ {A τ τ''}
        → {S : 𝕊 τ}
        → {M M' : toCtx S ⊢C⦂ A ‼ τ''}
        → toCtx S ⊢C⦂ M == M'
        → [] ⊢C⦂ config-to-comp S M ==
      τ-subst (τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ'' τ'' τ τ refl)
      (config-to-comp S M')
remove-subst {A} {τ} {τ''} {S} {M} M==M' = 
    C-trans 
        (eq-subst 
            (cong 
                (λ x → τ-subst x (config-to-comp S M)) 
                (uip 
                    {p = refl} 
                    {q = (τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ'' τ'' τ τ refl)})
            ))
        (double-τ-subst 
            ((τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ'' τ'' τ τ refl)) 
            (M==N⇒confM==confN M==M')) 

soundness : ∀ {A τ τ' τ'' τ'''}
        → {S : 𝕊 τ} 
        → {S' : 𝕊 τ'}
        → {M : toCtx S ⊢C⦂ A ‼ τ''}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
        → (τ''+τ≡τ'''+τ' : τ''' + τ' ≡ τ'' + τ)
        → (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩)
        → [] ⊢C⦂ 
            config-to-comp S M
            == 
            τ-subst (τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ''' τ'' τ' τ τ''+τ≡τ'''+τ') (config-to-comp S' M')
soundness refl (APP {M = M'} {V = V'}) = 
    remove-subst (fun-beta M' V')
soundness refl (MATCH {V = V} {W = W} {M = N}) = 
    remove-subst (match-beta V W N)
soundness {A} {τ} {τ'} {τ''} {τ'''} {S} {M = M} p (SEQ-FST τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = 
   {!   !}
soundness refl (SEQ-RET {V = V} {N = N}) = 
    remove-subst (seq-return V N)
soundness refl (SEQ-OP {op = op} {V = V} {M = M} {N = N}) = 
    remove-subst (seq-perform op V M N)
soundness {A} {τ} {.(τ + τ')} {.(τ' + τ''')} {τ'''} {S = S} {M = M} p (DELAY {τ' = τ'}) =
    C-trans 
        (eq-subst 
            (cong 
                (λ x → τ-subst x (config-to-comp S M)) 
                (uip 
                    {p = refl} 
                    {q = trans ((sym (+-assoc τ τ' τ'''))) ((τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ''' (τ' + τ''') (τ + τ') τ p))})))
        (eq-subst 
            (τ-subst-trans 
                ((sym (+-assoc τ τ' τ'''))) 
                ((τ+τ₂≡τ₁+τ₄⇒τ₂+τ≡τ₄+τ₂ τ''' (τ' + τ''') (τ + τ') τ p)) 
                (config-to-comp S M)))
soundness refl (HANDLE-RET {V = V} {H = H} {N = N}) = 
    remove-subst (handle-return V H N)
soundness p (HANDLE-STEP τ≤τ₄ τ+τ₂≡τ₄+τ₃ sucState M↝M') = {!   !}
soundness {A} {τ} {τ'} {τ''} {τ'''} {S = S} {M = M} p (HANDLE-OP {op = op}) = {!   !}
soundness {S = S} refl BOX = 
    remove-subst {S = S} C-refl
soundness refl (UNBOX p₁) = {!   !} 


