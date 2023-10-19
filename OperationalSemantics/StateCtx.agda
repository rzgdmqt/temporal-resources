module OperationalSemantics.StateCtx where

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Types

open import Data.Empty
open import Util.Equality
open import Data.Product
open import Util.Time

-------------------------
-- Definition of state --
-------------------------

data SCtx : Set where
    []ₛ     : SCtx
    _∷ₛ[_]_ : (Δ : SCtx) → (τ : Time) → (A : VType) → SCtx
    _⟨_⟩ₛ   : (Δ : SCtx) → (τ : Time) → SCtx

SCtx→Ctx : SCtx → Ctx
SCtx→Ctx []ₛ = []
SCtx→Ctx (Δ ∷ₛ[ τ ] A) = (SCtx→Ctx Δ) ∷ ([ τ ] A)
SCtx→Ctx (Δ ⟨ τ ⟩ₛ) = (SCtx→Ctx Δ) ⟨ τ ⟩

data 𝕊 : SCtx → Set where
    ∅     : 𝕊 ([]ₛ)
    _⟨_⟩ₘ : ∀ {Δ} → 𝕊 Δ → (τ : Time) → 𝕊 (Δ  ⟨ τ ⟩ₛ)  
    _∷ₘ_ : ∀ {Δ A τ} → 𝕊 Δ → (SCtx→Ctx (Δ ⟨ τ ⟩ₛ) ⊢V⦂ A) → 𝕊 (Δ ∷ₛ[ τ ] A)

toCtx : ∀ {Δ} → 𝕊 Δ → Ctx
toCtx ∅ = []
toCtx (S ⟨ τ ⟩ₘ) = (toCtx S) ⟨ τ ⟩
toCtx (_∷ₘ_ {A = A₁} {τ = τ} S A) = (toCtx S ∷ [ τ ] A₁)

-- lemma that context from state is equal to context from state context

SCtx→CtxΔ≡toCtxS : ∀ {Δ} → (S : 𝕊 Δ) → SCtx→Ctx Δ ≡ toCtx S
SCtx→CtxΔ≡toCtxS ∅ = refl
SCtx→CtxΔ≡toCtxS (S ⟨ τ ⟩ₘ) = cong (_⟨ τ ⟩) (SCtx→CtxΔ≡toCtxS S)
SCtx→CtxΔ≡toCtxS (_∷ₘ_ {A = A₁} {τ = τ} S A) = cong (_∷ [ τ ] A₁) (SCtx→CtxΔ≡toCtxS S)

-- Relation that tells that S' is a successor of S

data _≤ₛ_ : ∀ {Δ Δ'} → 𝕊 Δ → 𝕊 Δ' → Set where
    id-suc : ∀ {Δ} 
            → {S : 𝕊 Δ} 
            -----------
            → S ≤ₛ S

    ⟨⟩-suc : ∀ {Δ Δ'}
            → {S : 𝕊 Δ} 
            → {S' : 𝕊 Δ'} 
            → (τ'' : Time) 
            → S ≤ₛ S' 
            --------------------
            → S ≤ₛ (S' ⟨ τ'' ⟩ₘ)

    ∷-suc : ∀ {Δ Δ' τ A} 
            → {S : 𝕊 Δ} 
            → {S' : 𝕊 Δ'} 
            → (V : (SCtx→Ctx (Δ' ⟨ τ ⟩ₛ)) ⊢V⦂ A) 
            → S ≤ₛ S' 
            ----------------
            → S ≤ₛ (S' ∷ₘ V)

state-time : ∀ {Δ} → (S : 𝕊 Δ) → Time
state-time ∅ = 0
state-time (S ⟨ τ ⟩ₘ) = state-time S + τ
state-time (S ∷ₘ A) = state-time S

-- lemma that ctx-time of toCtx S is the same as state-time S

ctx-time≡state-time : ∀ {Δ} → (S : 𝕊 Δ) → ctx-time (toCtx S) ≡ (state-time S)
ctx-time≡state-time ∅ = refl 
ctx-time≡state-time (S ⟨ τ ⟩ₘ) = cong (_+ τ) (ctx-time≡state-time S)
ctx-time≡state-time (S ∷ₘ A) = ctx-time≡state-time S

-- if two states are successors they can be renamed contexts

≤ₛ⇒Ren : ∀ {Δ Δ'} → {S : 𝕊 Δ} → {S' : 𝕊 Δ'} → S ≤ₛ S' → Ren (toCtx S) (toCtx S')
≤ₛ⇒Ren id-suc = id-ren
≤ₛ⇒Ren (⟨⟩-suc τ'' y) = wk-⟨⟩-ren ∘ʳ (≤ₛ⇒Ren y)
≤ₛ⇒Ren (∷-suc V y) = wk-ren ∘ʳ (≤ₛ⇒Ren y)

-- ≤ₛ increase time

S≤ₛS'⇒τ≤τ' : ∀ {Δ Δ'} → {S : 𝕊 Δ} → {S' : 𝕊 Δ'} → S ≤ₛ S' → (state-time S) ≤ (state-time S')
S≤ₛS'⇒τ≤τ' {S = S} {S' = .S} id-suc = ≤-refl
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ⟨ τ'' ⟩ₘ)} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') = 
    ≤-stepsʳ τ'' 
        (τ-≤-substᵣ (sym (ctx-time≡state-time S')) 
        (τ-≤-substₗ (ctx-time≡state-time S) 
    (ren-≤-ctx-time (≤ₛ⇒Ren S≤ₛS'))))
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ∷ₘ V)} (∷-suc {S' = S'} V S≤ₛS') = 
    τ-≤-substᵣ (sym (ctx-time≡state-time S')) 
    (τ-≤-substₗ (ctx-time≡state-time S) 
    (ren-≤-ctx-time (≤ₛ⇒Ren S≤ₛS')))

-- lemma: if one state is successor of another then time pass at the end 
-- can be substituted

in-past-state : ∀ {Δ Δ'} 
                → {τ'' τ''' τ'''' : Time} 
                → {A : VType} 
                → {S : 𝕊 Δ} 
                → {S' : 𝕊 Δ'} 
                → S ≤ₛ S' 
                → (M : toCtx S ⟨ τ'' ⟩ ⊢C⦂ A ‼ τ'''') →(q : τ'' ≤ τ''') 
                → toCtx S' ⟨ τ''' ⟩ ⊢C⦂ A ‼ τ''''
in-past-state id-suc M q = C-rename (⟨⟩-≤-ren q) M
in-past-state (⟨⟩-suc τ'' S≤ₛS') M q = 
    C-rename (cong-⟨⟩-ren wk-⟨⟩-ren) (in-past-state S≤ₛS' M q)
in-past-state (∷-suc V S≤ₛS') M q = 
    C-rename (cong-⟨⟩-ren wk-ren) (in-past-state S≤ₛS' M q)

-- if one state is suc of another and final times are equal then states can rename

suc-comp-ren : ∀ {Δ Δ'} 
        → { τ'' τ''' : Time} 
        → {S : 𝕊 Δ} 
        → {S' : 𝕊 Δ'} 
        → S ≤ₛ S' 
        → (q : state-time S + τ'' ≤ state-time S' + τ''') 
        → Ren (toCtx S ⟨ τ'' ⟩) (toCtx S' ⟨ τ''' ⟩)
suc-comp-ren {S = S} id-suc q = ⟨⟩-≤-ren (+-cancelˡ-≤ (state-time S) q)
suc-comp-ren {τ'' = τ} {τ'''} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') q = 
    ⟨⟩-μ-ren ∘ʳ (suc-comp-ren S≤ₛS' (τ-≤-substᵣ (sym (+-assoc (state-time S') τ'' τ''')) q))
suc-comp-ren (∷-suc V S≤ₛS') q = (cong-⟨⟩-ren wk-ren) ∘ʳ (suc-comp-ren S≤ₛS' q)

-- suc relation is reflexive

suc-state-refl : ∀ {Δ} → {S : 𝕊 Δ} → S ≤ₛ S
suc-state-refl = id-suc


-- suc relation is transitive

suc-state-trans : ∀ {Δ Δ' Δ''} → {S : 𝕊 Δ} → {S' : 𝕊 Δ'} → {S'' : 𝕊 Δ''} → 
            S ≤ₛ S' → S' ≤ₛ S'' → S ≤ₛ S''
suc-state-trans id-suc S'≤ₛS'' = S'≤ₛS''
suc-state-trans (⟨⟩-suc τ'' S≤ₛS') id-suc = ⟨⟩-suc τ'' S≤ₛS'
suc-state-trans (⟨⟩-suc τ'' S≤ₛS') (⟨⟩-suc τ''' S'≤ₛS'') = 
    ⟨⟩-suc τ''' (suc-state-trans (⟨⟩-suc τ'' S≤ₛS') S'≤ₛS'')
suc-state-trans (⟨⟩-suc τ'' S≤ₛS') (∷-suc V S'≤ₛS'') = 
    ∷-suc V (suc-state-trans (⟨⟩-suc τ'' S≤ₛS') S'≤ₛS'')
suc-state-trans (∷-suc V S≤ₛS') id-suc = ∷-suc V S≤ₛS'
suc-state-trans (∷-suc V S≤ₛS') (⟨⟩-suc τ''' S'≤ₛS'') = 
    ⟨⟩-suc τ''' (suc-state-trans (∷-suc V S≤ₛS') S'≤ₛS'')
suc-state-trans (∷-suc V S≤ₛS') (∷-suc V₁ S'≤ₛS'') = 
    ∷-suc V₁ (suc-state-trans (∷-suc V S≤ₛS') S'≤ₛS'')


-- if states are suc of one another they must have equal time

aux-suc-state-antisym : ∀ {Δ Δ'} → {S : 𝕊 Δ} → {S' : 𝕊 Δ'} → 
            S ≤ₛ S' → S' ≤ₛ S → state-time S' ≡ state-time S
aux-suc-state-antisym id-suc S'≤ₛS = refl
aux-suc-state-antisym (⟨⟩-suc τ'' S≤ₛS') id-suc = refl
aux-suc-state-antisym (⟨⟩-suc τ'' S≤ₛS') (⟨⟩-suc τ''' S'≤ₛS) = 
    a≤b⇒b≤a⇒a≡b 
        (≤-trans (S≤ₛS'⇒τ≤τ' S'≤ₛS) (≤-stepsʳ τ''' ≤-refl)) 
        (≤-trans (S≤ₛS'⇒τ≤τ' S≤ₛS') (≤-stepsʳ τ'' ≤-refl))
aux-suc-state-antisym (⟨⟩-suc τ'' S≤ₛS') (∷-suc V S'≤ₛS) = 
    a≤b⇒b≤a⇒a≡b 
        (S≤ₛS'⇒τ≤τ' S'≤ₛS) 
        (≤-trans (S≤ₛS'⇒τ≤τ' S≤ₛS') (≤-stepsʳ τ'' ≤-refl))
aux-suc-state-antisym (∷-suc V S≤ₛS') id-suc = refl
aux-suc-state-antisym (∷-suc V S≤ₛS') (⟨⟩-suc τ''' S'≤ₛS) = 
    a≤b⇒b≤a⇒a≡b 
        (≤-trans (S≤ₛS'⇒τ≤τ' S'≤ₛS) 
        (≤-stepsʳ τ''' ≤-refl)) (S≤ₛS'⇒τ≤τ' S≤ₛS')
aux-suc-state-antisym (∷-suc V S≤ₛS') (∷-suc V₁ S'≤ₛS) = 
    a≤b⇒b≤a⇒a≡b 
        (S≤ₛS'⇒τ≤τ' S'≤ₛS) 
        (S≤ₛS'⇒τ≤τ' S≤ₛS')

-- operations on state - just for better readability in perservation theorem

time-pass : ∀ {Δ} → (S : 𝕊 Δ) → (τ' : Time) → 𝕊 (Δ ⟨ τ' ⟩ₛ)
time-pass S τ = S ⟨ τ ⟩ₘ 

extend-state : ∀ {Δ A τ'} → (S : 𝕊 Δ) → (SCtx→Ctx (Δ ⟨ τ' ⟩ₛ) ⊢V⦂ A) → 𝕊 (Δ ∷ₛ[ τ' ] A)
extend-state S V = S ∷ₘ V 

-- Lemmas about what can and what can't be in toCtx S (only var can be)

⇒-not-in-toCtx : ∀ {Δ τ} {S : 𝕊 Δ} {A : VType} {C : CType} → A ⇒ C ∈[ τ ] toCtx S → ⊥
⇒-not-in-toCtx {S = S ⟨ τ ⟩ₘ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {S = S ∷ₘ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Δ τ} {S : 𝕊 Δ} {A B : VType} → A |×| B ∈[ τ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₘ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Δ τ} {S : 𝕊 Δ} → Empty ∈[ τ ] toCtx S → ⊥
Empty-not-in-toCtx {S = S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ x) = Empty-not-in-toCtx x
Empty-not-in-toCtx {S = S ∷ₘ V} (Tl-∷ x) = Empty-not-in-toCtx x

not-in-empty-ctx : {τ : Time} {A : VType} → A ∈[ τ ] [] → ⊥
not-in-empty-ctx ()

var-in-ctx : ∀ { Γ τ' A} → 
            (V : Γ ⊢V⦂ [ τ' ] A) → 
            Σ[ τ'' ∈ Time ] ([ τ' ] A ∈[ τ'' ] Γ )
var-in-ctx (var {τ = τ} x) = τ , x

---------------------------------------
--  resource-lookup related lemmas   --
---------------------------------------

-- general resource-lookup lemma

resource-lookup : ∀ {Δ τ' τ'' A} → (S : 𝕊 Δ) →
                (x : [ τ' ] A ∈[ τ'' ] toCtx S) →
                (toCtx S -ᶜ τ'') ⟨ τ' ⟩ ⊢V⦂ A
resource-lookup (S ⟨ τ'' ⟩ₘ) (Tl-⟨⟩ {τ' = τ'} x) = 
    V-rename (cong-⟨⟩-ren (η-⟨⟩--ᶜ-ren τ' τ'')) (resource-lookup S x)
resource-lookup (_∷ₘ_ {τ = τ} S V) Hd = 
    V-rename (cong-⟨⟩-ren wk-ren) (V-rename (eq-ren (SCtx→CtxΔ≡toCtxS (S ⟨ τ ⟩ₘ))) V)
resource-lookup (S ∷ₘ V) (Tl-∷ {τ = τ} x) = 
    V-rename (cong-⟨⟩-ren (wk-ren -ʳ τ)) (resource-lookup S x)

-- renaming of the result of previous lemma to context S

resource-pass-to-ctx : ∀ {Δ τ' τ'' A} → (S : 𝕊 Δ) → 
            (p : τ' ≤ τ'') → 
            (q : τ'' ≤ state-time S) → 
            (V : (toCtx S -ᶜ τ'') ⟨ τ' ⟩ ⊢V⦂ A) → 
            toCtx S ⊢V⦂ A
resource-pass-to-ctx S p q V = V-rename (wk-⟨⟩--ᶜ-ren p (τ-≤-substᵣ (ctx-time≡state-time S) q)) V

-- lemma that allows us to pass exact time further

push-time-further : ∀ {Γ A τ τ'} → 
                (p : τ ≤ ctx-time Γ) →
                (x : A ∈[ τ' ] Γ -ᶜ τ ) → 
                Σ[ τ'' ∈ Time ] (τ + τ' ≤ τ'' × A ∈[ τ'' ] Γ )
push-time-further {Γ} {A} {τ} {τ'} p x = (var-rename (-ᶜ-⟨⟩-ren τ p) (Tl-⟨⟩ {τ = τ} x))

-- lemma that ensure that variable is distant to head of context 
-- for at most ctx-time 

from-head-time-positive : ∀ {Γ A τ} →
                        (x : A ∈[ τ ] Γ) → 
                        τ ≤ ctx-time Γ
from-head-time-positive Hd = z≤n
from-head-time-positive (Tl-∷ x) = from-head-time-positive x
from-head-time-positive {Γ = Γ ⟨ τ' ⟩} { τ = .(τ' + τ'')} (Tl-⟨⟩ {τ = τ'} {τ''} x) = 
    τ-≤-substᵣ (sym (+-comm τ' (ctx-time Γ))) (≤-extend τ' τ'' (ctx-time Γ) (from-head-time-positive x))
 
------------------------
-- spliting the state --
------------------------

data _⊢_,_⊢_SSplit_⊢_ : (Δ : SCtx) → (S : 𝕊 Δ) 
                    → (Δ' : SCtx) → (S' : 𝕊 Δ') 
                    → (Δ'' : SCtx) → (S'' : 𝕊 Δ'') 
                    → Set where
    SSplit-[] : ∀ {Δ} 
                → {S : 𝕊 Δ} 
                ------------------------------
                → Δ ⊢ S , []ₛ ⊢ ∅ SSplit Δ ⊢ S

    SSplit-∷  : ∀ {Δ Δ' Δ'' A τ}
                → {ρ : Ren (SCtx→Ctx Δ') (SCtx→Ctx Δ'')}
                → {S : 𝕊 Δ}  
                → {S' : 𝕊 Δ'}  
                → {S'' : 𝕊 Δ''}
                → {V : SCtx→Ctx (Δ' ⟨ τ ⟩ₛ) ⊢V⦂ A }  
                → Δ ⊢ S , Δ' ⊢ S' SSplit Δ'' ⊢ S'' 
                ------------------------------------------------------------------------------------------
                → Δ ⊢ S , Δ' ∷ₛ[ τ ] A ⊢ S' ∷ₘ V SSplit Δ'' ∷ₛ[ τ ] A ⊢ (S'' ∷ₘ V-rename (cong-⟨⟩-ren ρ) V)

    SSplit-⟨⟩  : ∀ {Δ Δ' Δ'' τ}
                → {ρ : Ren (SCtx→Ctx Δ') (SCtx→Ctx Δ'')}
                → {S : 𝕊 Δ}  
                → {S' : 𝕊 Δ'}  
                → {S'' : 𝕊 Δ''}  
                → Δ ⊢ S , Δ' ⊢ S' SSplit Δ'' ⊢ S'' 
                ---------------------------------------------------------------
                → Δ ⊢ S , Δ' ⟨ τ ⟩ₛ ⊢ S' ⟨ τ ⟩ₘ SSplit Δ'' ⟨ τ ⟩ₛ ⊢ (S'' ⟨ τ ⟩ₘ)

