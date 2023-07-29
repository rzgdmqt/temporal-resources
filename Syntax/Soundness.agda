{-# OPTIONS --allow-unsolved-metas #-}
module Syntax.Soundness where

open import Syntax.EquationalTheory
open import Syntax.PerservationTheorem
open import Syntax.ProgressTheorem
open import Syntax.Types
open import Syntax.Contexts
open import Syntax.CompContext
open import Syntax.Language
open import Syntax.State
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
soundness {τ = τ} {τ' = .(τ + τ')} {τ'''} {S = S} {S' = S'} {M = M} {M' = M'} p (DELAY {τ' = τ'}) = 
    {!   !}
soundness refl (HANDLE-RET {V = V} {H} {N}) = 
    M==N⇒confM==confN (handle-return V H N)
soundness p (HANDLE-STEP τ≤τ₄ τ+τ₂≡τ₄+τ₃ sucState M↝M') = {!   !}
soundness p (HANDLE-OP {S = S} {op = op} {V = V} {M} {H} {N}) = {!   !}
soundness refl BOX = C-refl
soundness {S = S} refl (UNBOX p₁ {V} {M = M}) = {!   !}
    -- M==N⇒confM==confN {M = unbox p₁ V M} {!   !} 

-- another approach with hole contexts

-- conf-to-comp : ∀ {A τ} 
--         → (Cf : Config (A ‼ τ)) 
--         → (S : 𝕊 (Config.τ Cf))  -- this and next line are just to fix termination error in Agda
--         → S ≡ Config.state Cf 
--         → [] ⊢K[ Ctx→Bctx (toCtx S) ⊢ A ‼ (τ + Config.τ Cf) ]⦂ A ‼ (τ + Config.τ Cf)
-- conf-to-comp ⟨ .0 , ∅ , M ⟩ .∅ refl = []ₖ
-- conf-to-comp ⟨ .(_ + τ'') , S ⟨ τ'' ⟩ₘ , M ⟩ .(S ⟨ τ'' ⟩ₘ) refl = 
--     {!   !}
-- conf-to-comp ⟨ τ , S ∷ₘ[ τ' ] x , M ⟩ .(S ∷ₘ[ τ' ] x) refl = {!   !}