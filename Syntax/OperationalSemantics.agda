module Syntax.OperationalSemantics where


open import Util.Time
open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Syntax.State
open import Util.Operations
open import Util.Equality
open import Data.Nat.Base
open import Syntax.Substitutions
open import Syntax.Renamings
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Relation.Nullary

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)


τ-subst⟨⟩ : ∀ {Γ A B τ τ' τ''}
        → τ ≡ τ'
        → Γ ⟨ τ ⟩ ∷ B ⊢C⦂ A ‼ τ''
        --------------------------
        → Γ ⟨ τ' ⟩ ∷ B ⊢C⦂ A ‼ τ''

τ-subst⟨⟩ refl M = M

τ-subst : ∀ {Γ A τ τ'}
        → τ ≡ τ'
        → Γ ⊢C⦂ A ‼ τ
        ---------------
        → Γ ⊢C⦂ A ‼ τ'

τ-subst refl M = M

a+b∸a≡b : ∀ {a b} → {p : a ≤ b} → a + (b ∸ a) ≡ b 
a+b∸a≡b {a} {b} {p} = 
    begin 
        a + (b ∸ a) ≡⟨ sym (+-∸-assoc a p) ⟩ 
        (a + b) ∸ a ≡⟨ +-∸-comm {m = a} b {o = a} ≤-refl ⟩ 
        (a ∸ a) + b ≡⟨ cong (_+ b) (n∸n≡0 a) ⟩  
        0 + b 
    ∎

τ≡τ∸τ'+τ' : ∀ τ τ' → τ ∸ (τ' ∸ τ') ≡ τ
τ≡τ∸τ'+τ' τ τ' = 
    begin 
        τ ∸ (τ' ∸ τ') ≡⟨ cong (τ ∸_) (n∸n≡0 τ') ⟩  
        τ ∸ 0 ≡⟨ refl ⟩ 
        τ
    ∎

τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ : ∀ τ τ₁ τ₂ τ₃ → τ + (τ₁ + τ₂ + τ₃) ≡ τ + (τ₁ + (τ₂ + τ₃))
τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ τ τ₁ τ₂ τ₃ = 
    begin 
        τ + (τ₁ + τ₂ + τ₃) ≡⟨ cong (τ +_) (+-assoc τ₁ τ₂ τ₃) ⟩  
        τ + (τ₁ + (τ₂ + τ₃))
    ∎

τ-≤-substᵣ : ∀ {τ τ' τ''} → τ' ≡ τ'' → τ ≤ τ'' → τ ≤ τ'
τ-≤-substᵣ refl q = q

step-time-eq : ∀ τ τ₁ τ' τ'' τ''' → (q : τ + τ₁ ≡ τ'' + τ''') → τ + (τ₁ + τ') ≡ τ'' + (τ''' + τ')
step-time-eq τ τ₁ τ' τ'' τ''' q = 
    begin 
        τ + (τ₁ + τ') ≡⟨ sym (+-assoc τ τ₁ τ') ⟩
        (τ + τ₁) + τ' ≡⟨ cong (_+ τ') q ⟩
        (τ'' + τ''') + τ' ≡⟨ +-assoc τ'' τ''' τ' ⟩
        τ'' + (τ''' + τ')
    ∎


lemma : ∀ τ τ' τ₁ → τ ≤ τ₁ → τ + τ + (τ₁ ∸ τ + τ') ≡ τ + (τ₁ + τ')
lemma τ τ' τ₁ p =
    begin 
        τ + τ + (τ₁ ∸ τ + τ') ≡⟨ +-assoc τ τ (τ₁ ∸ τ + τ') ⟩  
        τ + (τ + (τ₁ ∸ τ + τ')) ≡⟨ cong (τ +_ ) (cong (τ +_) ( sym (+-∸-comm τ' p))) ⟩ 
        τ + (τ + (τ₁ + τ' ∸ τ)) ≡⟨ cong (τ +_ ) (cong (τ +_) (cong (_∸ τ) (+-comm τ₁ τ')) ) ⟩ 
        τ + (τ + (τ' + τ₁ ∸ τ)) ≡⟨ cong (τ +_ ) (cong (τ +_) (+-∸-assoc τ' p)) ⟩ 
        τ + (τ + (τ' + (τ₁ ∸ τ))) ≡⟨ cong (τ +_ ) (sym (+-assoc τ τ' (τ₁ ∸ τ))) ⟩ 
        τ + (τ + τ' + (τ₁ ∸ τ)) ≡⟨ cong (τ +_) (cong (_+ (τ₁ ∸ τ)) (+-comm τ τ')) ⟩
        τ + (τ' + τ + (τ₁ ∸ τ)) ≡⟨ cong (τ +_)  (+-assoc τ' τ (τ₁ ∸ τ))  ⟩
        τ + (τ' + (τ + (τ₁ ∸ τ))) ≡⟨ cong (τ +_) (cong (τ' +_) (a+b∸a≡b {a = τ } {b = τ₁} {p = p})) ⟩
        τ + (τ' + τ₁) ≡⟨ cong (τ +_) (+-comm τ' τ₁) ⟩
        τ + (τ₁ + τ')
    ∎

τ∸τ'≤τ : ∀ τ τ' → τ ∸ τ' ≤ τ
τ∸τ'≤τ zero zero = ≤-refl
τ∸τ'≤τ zero (suc τ') = ≤-refl
τ∸τ'≤τ (suc τ) zero = ≤-refl
τ∸τ'≤τ (suc τ) (suc τ') = ≤-trans (τ∸τ'≤τ τ τ') (n≤1+n τ)

m≡n⇒m≤n : ∀ {m n} → m ≡ n → m ≤ n
m≡n⇒m≤n {zero} {n} p = z≤n
m≡n⇒m≤n {suc m} {suc n} p = s≤s (m≡n⇒m≤n (suc-injective p))

⇒-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} {A : VType} {C : CType} → A ⇒ C ∈[ τ' ] toCtx S → ⊥
⇒-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ x) = ⇒-not-in-ctx x
⇒-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x₁} (Tl-∷ x) = ⇒-not-in-ctx x

⦉⦊-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} {A B : VType} → A |×| B ∈[ τ' ] toCtx S → ⊥
⦉⦊-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ y) = ⦉⦊-not-in-ctx y
⦉⦊-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x} (Tl-∷ y) = ⦉⦊-not-in-ctx y

Empty-not-in-ctx : {τ τ' : Time} {S : 𝕊 τ} → Empty ∈[ τ' ] toCtx S → ⊥
Empty-not-in-ctx {.(_ + τ'')} {.(τ'' + _)} {S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ y) = Empty-not-in-ctx y
Empty-not-in-ctx {τ} {τ'} {S ∷ₘ[ τ'' ] x} (Tl-∷ y) = Empty-not-in-ctx y 

not-in-empty-ctx : {τ : Time} {A : VType} → A ∈[ τ ] [] → ⊥
not-in-empty-ctx ()


-- TODO: maybe rewrite this to ctx since it will be needed in equational theory as well
-- skip this resource-use part if you like yourself
{-
resource-use'' : ∀ {τ τ' τ'' A} → (S : 𝕊 τ) → 
                (p : τ' ≤ τ) →
                (q : toCtx S -ᶜ τ''' ≡ Γ) → 
                (x : [ τ' ] A ∈[ τ'' ] Γ) →
                toCtx S ⊢V⦂ A
-}

resource-use'' : ∀ {τ τ' τ'' A} → (S : 𝕊 τ) → 
                (p : τ' ≤ τ) →
                (x : [ τ' ] A ∈[ τ'' ] toCtx S -ᶜ τ') →
                toCtx S ⊢V⦂ A
resource-use''  ∅ z≤n ()
resource-use'' {τ' = zero} (S ⟨ τ'' ⟩ₘ) p (Tl-⟨⟩ x) = V-rename wk-⟨⟩-ren (resource-use'' S z≤n x)

resource-use'' {τ' = suc τ'} (S ⟨ τ'' ⟩ₘ) p x with suc τ' ≤? τ'' 
resource-use'' {_} {suc τ'} {τ₁} (_⟨_⟩ₘ {τ' = τ} S τ''') p (Tl-⟨⟩ {_} {τ₃} {τ₂} x) | yes q with suc τ' ≤? suc τ' 
... | yes r = {!!} --V-rename (⟨⟩-≤-ren q) (resource-use'' (S ⟨ suc τ' ⟩ₘ) (≤-stepsˡ τ ≤-refl) (proj₂ (proj₂ (var-rename (⟨⟩-ᶜ-ren' {τ = suc τ'}) x))))
... | no ¬r = ⊥-elim (¬r ≤-refl) 
resource-use'' {_} {suc τ'} (_⟨_⟩ₘ {τ} S zero) p x | no ¬q = 
    V-rename ⟨⟩-η⁻¹-ren (resource-use'' S (τ-≤-subst p (+-identityʳ τ)) x)
resource-use'' {_} {suc τ'} (S ⟨ suc τ'' ⟩ₘ) p x | no ¬q =
  V-rename wk-⟨⟩-ren (resource-use'' {τ' = τ' ∸ τ''} {τ'' = {!!}} S {!!} {!!})
  --  V-rename wk-⟨⟩-ren (resource-use'' S {!   !} {!   !} )

{-
resource-use'' {_} {suc τ'} (∅ ⟨ τ'' ⟩ₘ) p (Tl-⟨⟩ x) | yes q = V-rename wk-⟨⟩-ren (⊥-elim (not-in-empty-ctx x))
resource-use'' {_} {suc τ'} ((_⟨_⟩ₘ {τ₁} S τ''') ⟨ τ'' ⟩ₘ) p x | yes q = 
    V-rename ⟨⟩-μ-ren 
        (resource-use'' 
            (S ⟨ τ''' + τ'' ⟩ₘ) 
            (τ-≤-substᵣ (sym (+-assoc τ₁ τ''' τ'')) p) 
            (proj₂ (proj₂ (var-rename ({!   !} ∘ʳ ⟨⟩-μ⁻¹-ren) x)))) -- this is possible to prove
resource-use'' {_} {suc τ'} {A = A} ((_∷ₘ[_]_ {A = A₁} S τ'''  x₁) ⟨ τ'' ⟩ₘ) p (Tl-⟨⟩ x) | yes q  = {!   !} -- we should check if A = A₁ if yes we return it else we skip it

resource-use'' {_} {suc τ'} (∅ ⟨ τ'' ⟩ₘ) p x | no ¬q = 
    V-rename wk-⟨⟩-ren (⊥-elim (not-in-empty-ctx (proj₂ (proj₂ (var-rename (-ᶜ-wk-ren (suc τ' ∸ τ'')) x)))))
resource-use'' {_} {suc τ'} ((_⟨_⟩ₘ {τ₁} S τ''') ⟨ τ'' ⟩ₘ) p x | no ¬q = 
    V-rename ⟨⟩-μ-ren 
        (resource-use'' (S ⟨ (τ''' + τ'') ⟩ₘ) 
        ((τ-≤-substᵣ (sym (+-assoc τ₁ τ''' τ'')) p)) 
        (proj₂ (proj₂ (var-rename {!   !} x))))
resource-use'' {_} {suc τ'} ((S ∷ₘ[ τ''' ] x₁) ⟨ τ'' ⟩ₘ) p x | no ¬q = 
    V-rename (cong-⟨⟩-ren wk-ren) (resource-use'' (S ⟨ τ'' ⟩ₘ) p (proj₂ (proj₂ (var-rename {!   !} x)))) 
-}
resource-use'' {τ' = zero} (S ∷ₘ[ zero ] V) p Hd = V-rename (wk-ren ∘ʳ ⟨⟩-η-ren) V
resource-use'' {τ' = zero} (S ∷ₘ[ τ'' ] V) p (Tl-∷ x) = V-rename wk-ren (resource-use'' S p x)
resource-use'' {τ' = suc τ'} (S ∷ₘ[ τ'' ] V) p x = V-rename wk-ren (resource-use'' S p x)


data _↝_ :  {C D : CType} → Config C → Config D → Set where
    
    APP :   {A B : VType} {τ τ' : Time} 
            {S : 𝕊 τ} → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ τ'} → {V : (toCtx S) ⊢V⦂ A} →
            -------------------------------------------------------------
            ⟨ τ , S , lam M · V ⟩ ↝ ⟨ τ , S , M [ Hd ↦ V ]c ⟩

    MATCH : {τ : Time} {S : 𝕊 τ} {A B : VType} {C : CType} → 
            {V : toCtx S ⊢V⦂ A } →
            {W : toCtx S ⊢V⦂ B } → 
            {M : toCtx S ∷ A ∷ B ⊢C⦂ C} → 
            -------------------------------------------------------
            ⟨ τ , S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
            ⟨ τ , S , (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟩
    
    SEQ-FST : {τ τ₁ τ₂ τ₃ τ₄ : Time} → 
            {A B : VType} → {S : 𝕊 τ} → {S₁ : 𝕊 τ₁} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
            {N : ((toCtx S) ⟨ τ₂ ⟩ ∷ A) ⊢C⦂ B ‼ τ₃} → 
            {M' : toCtx S₁ ⊢C⦂ A ‼ τ₄} →
            (τ+τ₂≡τ₁+τ₄ : τ + τ₂ ≡ τ₁ + τ₄) →  
            (τ≤τ₁ : τ ≤ τ₁) → 
            (sucState : SucState S S₁) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ₁ , S₁ , M' ⟩ →
            --------------------------------------------------------------------
            ⟨ τ , S , M ; N ⟩ ↝ 
            ⟨ τ₁ , S₁ , M' ; (C-rename (cong-∷-ren (suc-comp-ren τ≤τ₁ sucState (C-rename wk-⟨⟩-ren M) (m≡n⇒m≤n τ+τ₂≡τ₁+τ₄))) N) ⟩  

    SEQ-RET : {τ τ' : Time} → 
            {A B : VType} → {S : 𝕊 τ} → 
            {V : (toCtx S) ⊢V⦂ A} 
            {N : ((toCtx S) ⟨ 0 ⟩ ∷ A) ⊢C⦂ B ‼ τ'} →  
            -----------------------------------------------------------------------------------
            ⟨ τ , S , return V ; N ⟩ ↝ ⟨ τ , S , C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟩
    
    SEQ-OP : {τ τ' τ'' : Time} → 
            {S : 𝕊 τ''} → 
            {op : Op} → 
            {A B : VType} → {S : 𝕊 τ''} → 
            {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ} →  
            {N : toCtx S ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
            -----------------------------------------------------------------------------------
            ⟨ τ'' , S , perform op V M ; N  ⟩ ↝ ⟨ τ'' , S ,  τ-subst (sym (+-assoc (op-time op) τ τ'))
                         (perform op V
                            (M ;
                             C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren))
                             N))  ⟩
    
    DELAY : {τ τ' τ'' : Time} → 
            {S : 𝕊 τ} →
            {A : VType} →  
            {M : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ τ''} → 
            ---------------------------------------------------------------------
            ⟨ τ , S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ τ + τ' , time-pass S τ' , M ⟩

    HANDLE-RET : {τ τ' : Time} →
            {S : 𝕊 τ} → 
            {A B : VType} → 
            {V : toCtx S ⊢V⦂ A} →
            {H : (op : Op) → (τ'' : Time) →
                toCtx S ∷ type-of-gtype (param op)
                  ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                ⊢C⦂ B ‼ (op-time op + τ'')} → 
            {N : toCtx S ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
            --------------------------------------------------------------------------
            ⟨ τ , S , handle return V `with H `in N ⟩ ↝ 
            ⟨ τ , S , (C-rename (cong-∷-ren ⟨⟩-η-ren) N) [ Hd ↦ V ]c ⟩ 
    
    HANDLE-STEP : {A B : VType} →
            {τ τ₁ τ₄ τ₆ τ₇ : Time} → 
            {S : 𝕊 τ} → 
            {S₁ : 𝕊 τ₇} → 
            {M : toCtx S ⊢C⦂ A ‼ τ₄} → 
            {H : (op : Op) → 
                 (τ₃ : Time) →
                 toCtx S ∷ type-of-gtype (param op)
                   ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₃)
                 ⊢C⦂ B ‼ (op-time op + τ₃)} → 
            {N : toCtx S ⟨ τ₄ ⟩ ∷ A ⊢C⦂ B ‼ τ₁} → 
            {M' : toCtx S₁  ⊢C⦂ A ‼ τ₆ } →  
            (τ≤τ₇ : τ ≤ τ₇) → 
            (τ+τ₄≡τ₇+τ₆ : τ + τ₄ ≡ τ₇ + τ₆) → 
            (sucState : SucState S S₁) → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ₇ , S₁ , M' ⟩ → 
            -----------------------------------------------------------------------
            ⟨ τ , S , handle M `with H `in N ⟩ ↝ 
            ⟨ τ₇ , S₁ , handle M' 
                        `with 
                            (λ op τ'' → C-rename (cong-∷-ren (cong-∷-ren (SucState⇒Ren τ≤τ₇ sucState))) (H op τ'')) 
                        `in (C-rename (cong-∷-ren (suc-comp-ren τ≤τ₇ sucState (C-rename wk-⟨⟩-ren M) (m≡n⇒m≤n τ+τ₄≡τ₇+τ₆))) 
                            N) ⟩

    HANDLE-OP : {τ τ' τ'' : Time} →
            {S : 𝕊 τ} → 
            {op : Op} → 
            {A B : VType} → 
            {V : toCtx S ⊢V⦂ type-of-gtype (param op)} →
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ''} →
            {H : (op : Op) → (τ₁ : Time) →
                toCtx S ∷ type-of-gtype (param op)
                  ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₁)
                ⊢C⦂ B ‼ (op-time op + τ₁)} → 
            {N : toCtx S ⟨ op-time op + τ'' ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
            --------------------------------------------------------------------------
            ⟨ τ , S , handle perform op V M `with H `in N ⟩ ↝
            ⟨ τ , S , 
            box (lam (handle M 
                    `with (λ op₁ τ''' → 
                            C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren))) 
                        (H op₁ τ''')) 
                    `in (C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)) 
                        N))) 
                ((H op (τ'' + τ')) [ Tl-∷ Hd ↦ V ]c) ⟩

    BOX :   {τ τ' τ'' : Time} → {S : 𝕊 τ} → {A B : VType} → 
            {V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A} →  
            {M : toCtx S ∷ [ τ' ] A ⊢C⦂ B ‼ τ''} →
            -----------------------------------------------------------------------
            ⟨ τ , S , (box V M) ⟩ ↝ ⟨ τ , extend-state S τ' V , M ⟩

    UNBOX : {τ τ' τ'' : Time} → {S : 𝕊 τ} →  {A : VType} → {C : CType} → 
            (p : τ' ≤ ctx-time (toCtx S)) → 
            {V : [ τ' ] A ∈[ τ'' ] toCtx S -ᶜ τ'} → 
            -- {V : (toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)} → -- TODO: put this back
            {M : toCtx S ∷ A ⊢C⦂ C } → 
            ---------------------------------------------------------------------------------------------
            ⟨ τ , S , unbox p (var V) M ⟩ ↝ ⟨ τ , S , M [ Hd ↦ resource-use'' S (τ-≤-subst p (ctx-timeSτ≡τ S)) V ]c ⟩


step-extends-state : {τ τ' τ'' τ''' : Time} → 
                {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ ) → 
                SucState S S'
step-extends-state APP = id-suc
step-extends-state MATCH = id-suc
step-extends-state SEQ-RET = id-suc
step-extends-state SEQ-OP = id-suc
step-extends-state HANDLE-RET = id-suc
step-extends-state (UNBOX p) = id-suc 
step-extends-state HANDLE-OP = id-suc
step-extends-state DELAY = ⟨⟩-suc ≤-refl _ id-suc
step-extends-state BOX = ∷-suc ≤-refl _ _ id-suc
step-extends-state (SEQ-FST {M = M} {M' = M'} τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState M↝M') = step-extends-state  M↝M'
step-extends-state (HANDLE-STEP {M = M} {M' = M'} τ≤τ₇ τ+τ₄≡τ₇+τ₆ sucState M↝M') = step-extends-state M↝M'

step-increases-time : {τ τ' τ'' τ''' : Time} → 
                {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ ) → 
                τ ≤ τ'
step-increases-time APP = ≤-refl
step-increases-time MATCH = ≤-refl
step-increases-time SEQ-RET = ≤-refl
step-increases-time SEQ-OP = ≤-refl
step-increases-time HANDLE-RET = ≤-refl
step-increases-time HANDLE-OP = ≤-refl
step-increases-time BOX = ≤-refl
step-increases-time (UNBOX p) = ≤-refl
step-increases-time (DELAY {τ' = τ'}) = ≤-stepsʳ τ' ≤-refl
step-increases-time (SEQ-FST τ+τ₂≡τ₁+τ₄ τ≤τ₁ sucState x) = τ≤τ₁
step-increases-time (HANDLE-STEP τ≤τ₇ τ+τ₄≡τ₇+τ₆ sucState x) = τ≤τ₇

data progresses : {τ' τ : Time} → 
                {S : 𝕊 τ} → 
                {A : VType} → 
                (M : toCtx S ⊢C⦂ A ‼ τ') →  Set where
                            
    is-value : {τ : Time} → 
            {S : 𝕊 τ} → 
            {A : VType} → 
            {V : toCtx S ⊢V⦂ A} →
            ---------------------
            progresses (return V) 
    
    is-op : {τ τ' : Time} → 
            {S : 𝕊 τ} → 
            {A : VType} → 
            {op : Op} → 
            {V : toCtx S ⊢V⦂ type-of-gtype (param op) } → 
            {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ'} → 
            --------------------------------------------------------------------
            progresses (perform op V M) 


    steps : {τ τ' τ'' τ''' : Time} → (q : τ ≤ τ') → 
            {S : 𝕊 τ} {S' : 𝕊 τ'} {A : VType} → 
            {M : toCtx S ⊢C⦂ A ‼ τ''} →
            {M' : toCtx S' ⊢C⦂  A ‼ τ''' } → 
            (p : τ + τ'' ≡ τ' + τ''') → 
            ⟨ τ , S , M ⟩ ↝ ⟨ τ' , S' , M' ⟩ →
            ----------------------------------
            progresses M 

progress : {τ τ' : Time} {S : 𝕊 τ} {A : VType} → (M : toCtx S ⊢C⦂ A ‼ τ') → progresses M 
progress (return V) = is-value
progress {τ} {τ'} {S = S} {A = A} ((_;_) {τ' = τ₁} M N) with progress M
... | is-value = steps ≤-refl refl SEQ-RET 
... | is-op = steps ≤-refl refl (SEQ-OP {S = S})
... | steps {τ' = τ₂} {τ'' = τ₃} {τ''' = τ₄} p q M↝M' = 
    steps p (step-time-eq τ τ₃ τ₁ τ₂ τ₄ q) (SEQ-FST q p (step-extends-state M↝M') M↝M')
progress {τ} {τ'} {S} (lam M · V) = steps ≤-refl refl APP
progress {τ} {τ'} (delay {τ' = τ₁} τ₂ M ) = steps (≤-stepsʳ τ₂ ≤-refl) (sym (+-assoc τ τ₂ τ₁)) DELAY
progress (match ⦉ V , W ⦊ `in M) = steps ≤-refl refl MATCH
progress (perform op V M) = is-op
progress {τ} (handle_`with_`in {τ' = τ₁} M H N) with progress M 
... | is-value = steps ≤-refl refl HANDLE-RET
... | is-op {τ' = τ'} {op = op} = steps ≤-refl (τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ τ (op-time op) τ' τ₁) HANDLE-OP
... | steps {τ' = τ₂} {τ'' = τ₃} {τ''' = τ₄} p q M↝M' = 
    steps p (step-time-eq τ τ₃ τ₁ τ₂ τ₄ q) (HANDLE-STEP p q (step-extends-state M↝M') M↝M')
progress (unbox τ≤ctx-time (var V) M) = steps ≤-refl refl (UNBOX τ≤ctx-time)
progress (box V M) = steps ≤-refl refl BOX
progress (absurd (var V)) = ⊥-elim (Empty-not-in-ctx V)
progress (var V · N) = ⊥-elim (⇒-not-in-ctx V)
progress (match var V `in M) = ⊥-elim (⦉⦊-not-in-ctx V)
