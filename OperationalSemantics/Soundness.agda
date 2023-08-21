{-# OPTIONS --allow-unsolved-metas #-}
module OperationalSemantics.Soundness where

open import OperationalSemantics.PerservationTheorem
open import OperationalSemantics.ProgressTheorem
open import OperationalSemantics.State

open import Syntax.CompContext
open import Syntax.Contexts
open import Syntax.EquationalTheory
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.Types

open import Util.Equality
open import Data.Empty
open import Util.Operations
open import Data.Product
open import Util.Time

≡to== : ∀ {Γ A τ}
        → {M N : Γ ⊢C⦂ A ‼ τ}
        → (M ≡ N)
        ---------------
        → Γ ⊢C⦂ M == N
≡to== refl = C-refl

τ-subst-cong : ∀ {Γ A τ τ'}
        → {M M' : Γ ⊢C⦂ A ‼ τ}
        → (p : τ ≡ τ')
        → (q : τ ≡ τ')
        → (Γ ⊢C⦂ M == M')
        ----------------------------------
        → Γ ⊢C⦂ τ-subst p M == τ-subst q M'
τ-subst-cong refl refl M==M' = M==M'

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

config-to-comp-cong : ∀ {A τ τ'}
        → {S : 𝕊 τ}
        → {M M' : toCtx S ⊢C⦂ A ‼ τ'}
        → toCtx S ⊢C⦂ M == M'
        → [] ⊢C⦂ 
            config-to-comp S M 
            == 
            config-to-comp S M' 
config-to-comp-cong {τ = .0} {τ'} {S = ∅} {M = M} {M' = M'} M==M' = 
    M==M'
config-to-comp-cong {τ = .(τ''' + τ'')} {τ'} {S = _⟨_⟩ₘ {τ'''} S τ''} {M = M} {M' = M'} M==M' = 
    τ-subst-cong 
        (sym (+-assoc τ''' τ'' τ')) 
        (sym (+-assoc τ''' τ'' τ')) 
        (config-to-comp-cong (delay-cong M==M'))
config-to-comp-cong {τ = τ} {S = S ∷ₘ[ τ' ] x} {M = M} {M' = M'} M==M' = 
    config-to-comp-cong (box-cong V-refl M==M') 

τ-subst-k : ∀ {Γ Δ A C τ τ'}
    → τ ≡ τ'
    → Γ ⊢K[ Δ ⊢ C ]⦂ A ‼ τ
    → Γ ⊢K[ Δ ⊢ C ]⦂ A ‼ τ'
τ-subst-k refl K = K

-----------------------
-- Soundness theorem --
-----------------------

soundness : ∀ {A τ τ' τ'' τ'''}
        → {S : 𝕊 τ} 
        → {S' : 𝕊 τ'}
        → {M : toCtx S ⊢C⦂ A ‼ τ''}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
        → (p : τ' + τ''' ≡ τ + τ'')
        → (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩)
        → [] ⊢C⦂ 
            config-to-comp S M
            == 
            τ-subst p (config-to-comp S' M')
soundness refl (APP {M = M} {V = V})  = 
    config-to-comp-cong (fun-beta M V)
soundness refl (MATCH {V = V} {W = W} {M = M}) = 
    config-to-comp-cong (match-beta V W M)
soundness {S = S} p (SEQ-FST {S = S} {S₁ = .S} {M = M} {N = N} {M₁} τ+τ₂≡τ₁+τ₄ id-suc M↝M') with soundness (sym τ+τ₂≡τ₁+τ₄) M↝M' 
... | M==M' = {!   !}
soundness {S = S} p (SEQ-FST {S = S} {S₁ = .(_ ⟨ τ'' ⟩ₘ)} {M = M} {N = N} {M₁} τ+τ₂≡τ₁+τ₄ (⟨⟩-suc τ'' S≤ₛS') M↝M') with soundness (sym τ+τ₂≡τ₁+τ₄) M↝M' 
... | M==M' = {!   !} 
soundness {S = S} p (SEQ-FST {S = S} {S₁ = .(_ ∷ₘ[ τ'' ] V)} {M = M} {N = N} {M₁} τ+τ₂≡τ₁+τ₄ (∷-suc τ'' V S≤ₛS') M↝M') with soundness (sym τ+τ₂≡τ₁+τ₄) M↝M' 
... | M==M' = {!   !} 
soundness refl (SEQ-RET {V = V} {N = N}) = 
    config-to-comp-cong (seq-return V N)
soundness refl (SEQ-OP {op = op} {V = V} {M = M} {N = N}) =     
    config-to-comp-cong (seq-perform op V M N)
soundness {A} {τ} {τ''' = τ'''} {S = S} {M = M} p (DELAY {τ' = τ'}) = 
    C-trans 
        (≡to== 
            (cong (λ x → τ-subst x (config-to-comp S M)) 
            (uip 
                {p = refl} 
                {q = trans (sym (+-assoc τ τ' τ''')) p}))) 
        (≡to== 
            (τ-subst-trans 
                (sym (+-assoc τ τ' τ''')) 
                p 
                (config-to-comp S M)))
soundness refl (HANDLE-RET {V = V} {H = H} {N = N}) = 
    config-to-comp-cong (handle-return V H N)
soundness p (HANDLE-STEP τ+τ₂≡τ₄+τ₃ S≤ₛS' M↝M') with soundness (sym τ+τ₂≡τ₄+τ₃) M↝M'
... | M==M' = {!   !}
soundness {S = S} p (HANDLE-OP {op = op} {V = V} {M = M} {H = H} {N = N}) = 
    C-trans 
        (config-to-comp-cong 
            (handle-perform op V M H N)) 
        {!   !}
soundness refl (BOX {S = S}) = 
    config-to-comp-cong {S = S} C-refl
soundness {S = ∅} refl (UNBOX {S = .∅} z≤n) = 
    {!   !}  -- we don't have any resources so this would imply ill-scoped program
soundness {A} {τ} {τ} {τ''} {τ''} {S =  _⟨_⟩ₘ {τ''''} S τ'''} refl (UNBOX {τ' = τ'} p₁ {V = V} {M = M}) = 
    τ-subst-cong 
        (sym (+-assoc τ'''' τ''' τ'')) 
        (sym (+-assoc τ'''' τ''' τ'')) 
        {!   !} -- delay cong
soundness {S = S ∷ₘ[ τ' ] V} refl (UNBOX {S = .(S ∷ₘ[ τ' ] V)} p₁ {V = W}) = {!   !} -- we split case wether W ≡ V or not. if yes, unbox-beta else cong-box recursive call 