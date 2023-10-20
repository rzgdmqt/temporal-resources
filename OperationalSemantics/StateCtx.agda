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

data 𝕊 : Ctx → Set where
    ∅     : 𝕊 ([])
    _⟨_⟩ₘ : ∀ {Γ} → 𝕊 Γ → (τ : Time) → 𝕊 (Γ ⟨ τ ⟩)  
    _∷ₘ_ : ∀ {Γ A τ} → 𝕊 Γ → ((Γ ⟨ τ ⟩) ⊢V⦂ A) → 𝕊 (Γ ∷ ([ τ ] A))

toCtx : ∀ {Γ} → 𝕊 Γ → Ctx
toCtx ∅ = []
toCtx (S ⟨ τ ⟩ₘ) = (toCtx S) ⟨ τ ⟩
toCtx (_∷ₘ_ {A = A₁} {τ = τ} S A) = (toCtx S ∷ [ τ ] A₁)

-- lemma that context from state is equal to context from state context

Γ≡toCtxS : ∀ {Γ} → (S : 𝕊 Γ) → Γ ≡ toCtx S
Γ≡toCtxS ∅ = refl
Γ≡toCtxS (S ⟨ τ ⟩ₘ) = cong (_⟨ τ ⟩) (Γ≡toCtxS S)
Γ≡toCtxS (_∷ₘ_ {A = A₁} {τ = τ} S A) = cong (_∷ [ τ ] A₁) (Γ≡toCtxS S)

-- Relation that tells that S' is a successor of S

data _≤ₛ_ : ∀ {Γ Γ'} → 𝕊 Γ → 𝕊 Γ' → Set where
    id-suc : ∀ {Γ} 
            → {S : 𝕊 Γ} 
            -----------
            → S ≤ₛ S

    ⟨⟩-suc : ∀ {Γ Γ'}
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (τ'' : Time) 
            → S ≤ₛ S' 
            --------------------
            → S ≤ₛ (S' ⟨ τ'' ⟩ₘ)

    ∷-suc : ∀ {Γ Γ' τ A} 
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (V : (Γ' ⟨ τ ⟩) ⊢V⦂ A) 
            → S ≤ₛ S' 
            ----------------
            → S ≤ₛ (S' ∷ₘ V)

state-time : ∀ {Γ} → (S : 𝕊 Γ) → Time
state-time ∅ = 0
state-time (S ⟨ τ ⟩ₘ) = state-time S + τ
state-time (S ∷ₘ A) = state-time S

-- lemma that ctx-time of toCtx S is the same as state-time S

ctx-time≡state-time : ∀ {Γ} → (S : 𝕊 Γ) → ctx-time (toCtx S) ≡ (state-time S)
ctx-time≡state-time ∅ = refl 
ctx-time≡state-time (S ⟨ τ ⟩ₘ) = cong (_+ τ) (ctx-time≡state-time S)
ctx-time≡state-time (S ∷ₘ A) = ctx-time≡state-time S

-- if two states are successors they can be renamed contexts

≤ₛ⇒Ren : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → Ren (toCtx S) (toCtx S')
≤ₛ⇒Ren id-suc = id-ren
≤ₛ⇒Ren (⟨⟩-suc τ'' y) = wk-⟨⟩-ren ∘ʳ (≤ₛ⇒Ren y)
≤ₛ⇒Ren (∷-suc V y) = wk-ren ∘ʳ (≤ₛ⇒Ren y)

-- ≤ₛ increase time

S≤ₛS'⇒τ≤τ' : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → (state-time S) ≤ (state-time S')
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

in-past-state : ∀ {Γ Γ'} 
                → {τ'' τ''' τ'''' : Time} 
                → {A : VType} 
                → {S : 𝕊 Γ} 
                → {S' : 𝕊 Γ'} 
                → S ≤ₛ S' 
                → (M : toCtx S ⟨ τ'' ⟩ ⊢C⦂ A ‼ τ'''') →(q : τ'' ≤ τ''') 
                → toCtx S' ⟨ τ''' ⟩ ⊢C⦂ A ‼ τ''''
in-past-state id-suc M q = C-rename (⟨⟩-≤-ren q) M
in-past-state (⟨⟩-suc τ'' S≤ₛS') M q = 
    C-rename (cong-⟨⟩-ren wk-⟨⟩-ren) (in-past-state S≤ₛS' M q)
in-past-state (∷-suc V S≤ₛS') M q = 
    C-rename (cong-⟨⟩-ren wk-ren) (in-past-state S≤ₛS' M q)

-- if one state is suc of another and final times are equal then states can rename

suc-comp-ren : ∀ {Γ Γ'} 
        → { τ'' τ''' : Time} 
        → {S : 𝕊 Γ} 
        → {S' : 𝕊 Γ'} 
        → S ≤ₛ S' 
        → (q : state-time S + τ'' ≤ state-time S' + τ''') 
        → Ren (toCtx S ⟨ τ'' ⟩) (toCtx S' ⟨ τ''' ⟩)
suc-comp-ren {S = S} id-suc q = ⟨⟩-≤-ren (+-cancelˡ-≤ (state-time S) q)
suc-comp-ren {τ'' = τ} {τ'''} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') q = 
    ⟨⟩-μ-ren ∘ʳ (suc-comp-ren S≤ₛS' (τ-≤-substᵣ (sym (+-assoc (state-time S') τ'' τ''')) q))
suc-comp-ren (∷-suc V S≤ₛS') q = (cong-⟨⟩-ren wk-ren) ∘ʳ (suc-comp-ren S≤ₛS' q)

-- suc relation is reflexive

suc-state-refl : ∀ {Γ} → {S : 𝕊 Γ} → S ≤ₛ S
suc-state-refl = id-suc


-- suc relation is transitive

suc-state-trans : ∀ {Γ Γ' Γ''} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → {S'' : 𝕊 Γ''} → 
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

aux-suc-state-antisym : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → 
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

time-pass : ∀ {Γ} → (S : 𝕊 Γ) → (τ' : Time) → 𝕊 (Γ ⟨ τ' ⟩)
time-pass S τ = S ⟨ τ ⟩ₘ 

extend-state : ∀ {Γ A τ'} → (S : 𝕊 Γ) → (Γ ⟨ τ' ⟩ ⊢V⦂ A) → 𝕊 (Γ ∷ ([ τ' ] A))
extend-state S V = S ∷ₘ V 

-- Lemmas about what can and what can't be in toCtx S (only var can be)

⇒-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A : VType} {C : CType} → A ⇒ C ∈[ τ ] toCtx S → ⊥
⇒-not-in-toCtx {S = S ⟨ τ ⟩ₘ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {S = S ∷ₘ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A B : VType} → A |×| B ∈[ τ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ τ'' ⟩ₘ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₘ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} → Empty ∈[ τ ] toCtx S → ⊥
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

resource-lookup : ∀ {Γ τ' τ'' A} → (S : 𝕊 Γ) →
                (x : [ τ' ] A ∈[ τ'' ] toCtx S) →
                (toCtx S -ᶜ τ'') ⟨ τ' ⟩ ⊢V⦂ A
resource-lookup (S ⟨ τ'' ⟩ₘ) (Tl-⟨⟩ {τ' = τ'} x) = 
    V-rename (cong-⟨⟩-ren (η-⟨⟩--ᶜ-ren τ' τ'')) (resource-lookup S x)
resource-lookup (_∷ₘ_ {τ = τ} S V) Hd = 
    V-rename (cong-⟨⟩-ren wk-ren) (V-rename (eq-ren (Γ≡toCtxS (S ⟨ τ ⟩ₘ))) V)
resource-lookup (S ∷ₘ V) (Tl-∷ {τ = τ} x) = 
    V-rename (cong-⟨⟩-ren (wk-ren -ʳ τ)) (resource-lookup S x)

-- renaming of the result of previous lemma to context S

resource-pass-to-ctx : ∀ {Γ τ' τ'' A} → (S : 𝕊 Γ) → 
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

data _⊢_,_⊢_SSplit_⊢_ : (Γ : Ctx) → (S : 𝕊 Γ) 
                    → (Γ' : Ctx) → (S' : 𝕊 Γ') 
                    → (Γ'' : Ctx) → (S'' : 𝕊 Γ'') 
                    → Set where
    SSplit-[] : ∀ {Γ} 
                → {S : 𝕊 Γ} 
                -----------------------------
                → Γ ⊢ S , [] ⊢ ∅ SSplit Γ ⊢ S

    SSplit-∷  : ∀ {Γ Γ' Γ'' A τ}
                → {ρ : Ren Γ' Γ''}
                → {S : 𝕊 Γ}  
                → {S' : 𝕊 Γ'}  
                → {S'' : 𝕊 Γ''}
                → {V : Γ' ⟨ τ ⟩ ⊢V⦂ A }  
                → Γ ⊢ S , Γ' ⊢ S' SSplit Γ'' ⊢ S'' 
                -------------------------------------------------------------------------------------------
                → Γ ⊢ S , Γ' ∷ [ τ ] A ⊢ S' ∷ₘ V SSplit Γ'' ∷ [ τ ] A ⊢ (S'' ∷ₘ V-rename (cong-⟨⟩-ren ρ) V)

    SSplit-⟨⟩  : ∀ {Γ Γ' Γ'' τ}
                → {S : 𝕊 Γ}  
                → {S' : 𝕊 Γ'}  
                → {S'' : 𝕊 Γ''}  
                → Γ ⊢ S , Γ' ⊢ S' SSplit Γ'' ⊢ S'' 
                --------------------------------------------------------------
                → Γ ⊢ S , Γ' ⟨ τ ⟩ ⊢ S' ⟨ τ ⟩ₘ SSplit Γ'' ⟨ τ ⟩ ⊢ (S'' ⟨ τ ⟩ₘ)

_++ₛ_ : ∀ {Γ Γ'} → (S : 𝕊 Γ) → (S' : 𝕊 Γ') → 𝕊 (Γ ++ᶜ Γ')
S ++ₛ ∅ = S
S ++ₛ (S' ⟨ τ ⟩ₘ) = (S ++ₛ S') ⟨ τ ⟩ₘ
S ++ₛ (S' ∷ₘ V) = (S ++ₛ S') ∷ₘ V-rename (cong-⟨⟩-ren (cong-ren {Γ = []} empty-ren ∘ʳ eq-ren (sym ++ᶜ-identityˡ))) V
