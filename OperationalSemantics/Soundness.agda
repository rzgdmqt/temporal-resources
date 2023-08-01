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

config-to-comp : ∀ {A τ} 
        → (Cf : Config (A ‼ τ)) 
        → (S : 𝕊 (Config.τ Cf))  -- this and next line are just to fix termination error in Agda
        → S ≡ Config.state Cf 
        → [] ⊢C⦂ A ‼ (τ + Config.τ Cf)
config-to-comp {τ = τ} ⟨ .0 , ∅ , M ⟩ _ _ = τ-subst (sym (+-identityʳ τ)) M
config-to-comp {τ = τ'} ⟨ .(τ + τ'') , _⟨_⟩ₘ {τ} S τ'' , M ⟩ .(S ⟨ τ'' ⟩ₘ) refl = 
    τ-subst (0+[τ''+τ'+τ]≡τ'+[τ+τ''] τ τ' τ'')
      (config-to-comp ⟨ τ , S , delay τ'' M ⟩ S refl)
config-to-comp ⟨ τ , S ∷ₘ[ τ' ] V , M ⟩ (.S ∷ₘ[ .τ' ] .V) refl = 
    config-to-comp ⟨ τ , S , box V M ⟩ S refl


-- lemma about passing equation under the config-to-comp

M==N⇒confM==confN : ∀ {A τ τ'}
        → {S : 𝕊 τ}
        → {M M' : toCtx S ⊢C⦂ A ‼ τ'}
        → toCtx S ⊢C⦂ M == M'
        → [] ⊢C⦂ 
            config-to-comp ⟨ τ , S , M ⟩ S refl
            == 
            config-to-comp ⟨ τ , S , M' ⟩ S refl
M==N⇒confM==confN {τ = .0} {τ'} {S = ∅} {M = M} {M' = M'} M==M' = 
    congruence M==M' (τ-subst (sym (+-identityʳ τ')))
M==N⇒confM==confN {τ = .(τ''' + τ'')} {τ'} {S = _⟨_⟩ₘ {τ'''} S τ''} {M = M} {M' = M'} M==M' = 
    congruence (M==N⇒confM==confN (delay-cong M==M')) (λ x → τ-subst (0+[τ''+τ'+τ]≡τ'+[τ+τ''] τ''' τ' τ'') x) 
M==N⇒confM==confN {τ = τ} {S = S ∷ₘ[ τ' ] x} {M = M} {M' = M'} M==M' = 
    M==N⇒confM==confN (box-cong V-refl M==M') 

τ-subst-merge : ∀ {Γ A}
        → {τ τ' τ'' : Time}
        → (p : τ ≡ τ'')
        → (q : τ ≡ τ')
        → (r : τ' ≡ τ'')
        → (M : Γ ⊢C⦂ A ‼ τ)
        → τ-subst p M ≡ τ-subst r (τ-subst q M)
τ-subst-merge refl refl refl M = refl

eq-subst : ∀ {Γ A τ}
        → {M M' N : Γ ⊢C⦂ A ‼ τ}
        → (M ≡ M')
        → Γ ⊢C⦂ N == M
        ---------------
        → Γ ⊢C⦂ N == M'
eq-subst refl N==M = N==M

-- Soundness theorem

soundness : ∀ {A τ τ' τ'' τ'''}
        → {S : 𝕊 τ} 
        → {S' : 𝕊 τ'}
        → {M : toCtx S ⊢C⦂ A ‼ τ''}
        → {M' : toCtx S' ⊢C⦂ A ‼ τ'''}
        → (τ''+τ≡τ'''+τ' : τ'' + τ ≡ τ''' + τ')
        → (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩)
        → [] ⊢C⦂ 
            config-to-comp ⟨ τ , S , M ⟩ S refl
            == 
            τ-subst (sym τ''+τ≡τ'''+τ') (config-to-comp ⟨ τ' , S' , M' ⟩ S' refl)
soundness refl (APP {M = M} {V = V}) = 
    M==N⇒confM==confN (fun-beta M V)
soundness refl (MATCH {V = V} {W} {M}) = 
    M==N⇒confM==confN (match-beta V W M)
soundness {τ = τ} {S = S} p (SEQ-FST {τ} {τ₁} {τ₂} {_} {τ₄} {M = M} {N} {M₁ = M₁} τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = {!   !}
soundness refl (SEQ-RET {V = V} {N}) = 
    M==N⇒confM==confN (seq-return V N)
soundness refl (SEQ-OP {op = op} {V = V} {M} {N}) = 
    M==N⇒confM==confN (seq-perform op V M N)
soundness {τ = τ} {τ' = .(τ + τ')} {.(τ' + τ''')} {τ'''} {S = S} {S' = .(time-pass S τ')} {M = .(delay τ' M')} {M' = M'} p (DELAY {τ' = τ'}) = 
    (eq-subst (τ-subst-merge refl p (τ'''+[τ+τ']≡τ'+τ'''+τ τ {! τ'  !} {!   !}) (config-to-comp ⟨ τ , S , delay τ' M' ⟩ S refl)) C-refl)
    -- eq-subst (τ-subst-merge {!   !} {!   !} {!   !} (τ-subst {!   !} ((config-to-comp ⟨ τ , S , delay τ' M' ⟩ S refl)))) {!   !}
soundness refl (HANDLE-RET {V = V} {H} {N}) = 
    M==N⇒confM==confN (handle-return V H N)
soundness p (HANDLE-STEP τ≤τ₄ τ+τ₂≡τ₄+τ₃ sucState M↝M') = {!   !}
soundness p (HANDLE-OP {S = S} {op = op} {V = V} {M} {H} {N}) = {!   !}
soundness refl BOX = C-refl
soundness {S = S} refl (UNBOX p₁ {V} {M = M}) =
    M==N⇒confM==confN {M = unbox p₁ V M} {!   !} 


-- -- another approach with hole contexts

-- -- program with typed hole in it
-- data _⊢[_⊢_]⦂_ (Γ : Ctx) : BCtx → CType → CType → Set where

--     []ₖ : ∀ {A τ} 
--         ---------------------------
--         → Γ ⊢[ []ₗ ⊢ A ‼ τ ]⦂ A ‼ τ
        
--     delayₖ : ∀ {Δ A C τ'}
--         → (τ : Time)
--         → Γ ⟨ τ ⟩ ⊢[ Δ ⊢ C ]⦂ A ‼ τ'
--         -----------------------------------------
--         → Γ ⊢[ ⟨ τ ⟩ₗ Δ ⊢ C ]⦂ A ‼ (τ + τ')

--     boxₖ : ∀ {Δ A B C τ τ'}
--         → Γ ⟨ τ ⟩ ⊢V⦂ A
--         → Γ ∷ [ τ ] A ⊢[ Δ ⊢ C ]⦂ B ‼ τ'
--         ---------------------------------------
--         → Γ ⊢[ [ τ ] A ∷ₗ Δ ⊢ C ]⦂ B ‼ τ'

-- -- hole filling function
-- -- _ₖ[_] : ∀ {Γ Δ D C} 
-- --         → (K : Γ ⊢[ Δ ⊢ D ]⦂ C) 
-- --         → (M : Γ ⋈ Δ ⊢C⦂ D) 
-- --         → Γ ⊢C⦂ C
-- -- []ₖ ₖ[ M ] = M
-- -- delayₖ τ K ₖ[ M ] = delay τ (K ₖ[ M ])
-- -- boxₖ V K ₖ[ M ] = box V (K ₖ[ M ])
