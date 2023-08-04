module OperationalSemantics.State where

open import Syntax.Types
open import Syntax.Language
open import Syntax.Contexts
open import Syntax.Renamings
open import Util.Time
open import Util.Properties
open import Util.Equality
open import Data.Empty
open import Data.Product

-------------------------
-- Definition of state --
-------------------------

mutual 
    data 𝕊 : (τ : Time) → Set where
        ∅ : 𝕊 0
        _⟨_⟩ₘ : {τ' : Time} → 𝕊 τ' → (τ'' : Time) → 𝕊 (τ' + τ'') 
        _∷ₘ[_]_ : {τ : Time} {A : VType} → (S : 𝕊 τ) → (τ' : Time) → (toCtx S) ⟨ τ' ⟩ ⊢V⦂ A → 𝕊 τ 

    toCtx : {τ : Time} → 𝕊 τ → Ctx
    toCtx ∅ = []
    toCtx (S ⟨ τ'' ⟩ₘ) = (toCtx S) ⟨ τ'' ⟩
    toCtx (_∷ₘ[_]_ {A = A₁} S τ' A) = (toCtx S) ∷ [ τ' ] A₁

-- Relation that tells that S' is a successor of S

data _≤ₛ_ : {τ τ' : Time} → 𝕊 τ → 𝕊 τ' → Set where
    id-suc : {τ : Time} → {S : 𝕊 τ} → S ≤ₛ S
    ⟨⟩-suc : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → (p : τ ≤ τ') → (τ'' : Time) → 
        S ≤ₛ S' → S ≤ₛ (S' ⟨ τ'' ⟩ₘ)
    ∷-suc : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → {A : VType} → 
        (p : τ ≤ τ') → (τ'' : Time) → (V : (toCtx S') ⟨ τ'' ⟩ ⊢V⦂ A) → 
        S ≤ₛ S' → S ≤ₛ (S' ∷ₘ[ τ'' ] V)

-- lemma that ctx-time of toCtx (S τ) is τ

ctx-timeSτ≡τ : {τ : Time} → (S : 𝕊 τ) → ctx-time (toCtx S) ≡ τ
ctx-timeSτ≡τ ∅ = refl
ctx-timeSτ≡τ (S ⟨ τ'' ⟩ₘ) = cong (_+ τ'') (ctx-timeSτ≡τ S)
ctx-timeSτ≡τ (S ∷ₘ[ τ' ] x) = ctx-timeSτ≡τ S

-- if two states are successors they can be renamed contexts

≤ₛ⇒Ren : {τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → (p : τ ≤ τ') → S ≤ₛ S' → Ren (toCtx S) (toCtx S')
≤ₛ⇒Ren p id-suc = id-ren
≤ₛ⇒Ren p (⟨⟩-suc p₁ τ'' y) = wk-⟨⟩-ren ∘ʳ (≤ₛ⇒Ren p₁ y)
≤ₛ⇒Ren p (∷-suc p₁ τ'' V y) = wk-ren ∘ʳ (≤ₛ⇒Ren p₁ y)

-- lemma: if one state is successor of another then time pass at the end 
-- can be substituted

in-past-state : {τ τ' τ'' τ''' τ'''' : Time} → 
                {A : VType} → 
                {S : 𝕊 τ} → 
                {S' : 𝕊 τ'} →  
                (p : τ ≤ τ') →  
                S ≤ₛ S' →  
                (M : toCtx S ⟨ τ'' ⟩ ⊢C⦂ A ‼ τ'''') →
                (q : τ'' ≤ τ''') →  
                toCtx S' ⟨ τ''' ⟩ ⊢C⦂ A ‼ τ''''
in-past-state {τ} {S = S} {S' = .S} p id-suc M q = C-rename (⟨⟩-≤-ren q) M
in-past-state {τ} {τ'} {τ''} {τ'''} {S = S} {S' = .(_ ⟨ τ₁ ⟩ₘ)} p (⟨⟩-suc {τ' = τ₂} p₁ τ₁ S≤ₛS') M q = 
    C-rename (cong-⟨⟩-ren wk-⟨⟩-ren) (in-past-state p₁ S≤ₛS' M q)
in-past-state {S = S} {S' = .(_ ∷ₘ[ τ'' ] V)} p (∷-suc p₁ τ'' V S≤ₛS') M q = 
        C-rename (cong-⟨⟩-ren wk-ren) (in-past-state p S≤ₛS' M q) 

-- if one state is suc of another and final times are equal then states can rename

suc-comp-ren : {τ τ' τ'' τ''' τ'''' : Time} → 
                {A : VType} → 
                {S : 𝕊 τ} → 
                {S' : 𝕊 τ'} →  
                (p : τ ≤ τ') →  
                S ≤ₛ S' →  
                (M : toCtx S ⟨ τ'' ⟩ ⊢C⦂ A ‼ τ'''') →
                (q : τ + τ'' ≤ τ' + τ''') →  
                Ren (toCtx S ⟨ τ'' ⟩) (toCtx S' ⟨ τ''' ⟩)
suc-comp-ren {τ} p id-suc M q = ⟨⟩-≤-ren (+-cancelˡ-≤ τ q)
suc-comp-ren {τ} {τ'} {τ'' = τ₂} {τ'''} p (⟨⟩-suc {τ' = τ₃} p₁ τ'' S≤ₛS') M q = 
        ⟨⟩-μ-ren ∘ʳ suc-comp-ren p₁ S≤ₛS' M (τ-≤-substᵣ (sym (+-assoc τ₃ τ'' τ''')) q)
suc-comp-ren p (∷-suc p₁ τ'' V S≤ₛS') M q = cong-⟨⟩-ren wk-ren ∘ʳ 
        suc-comp-ren p S≤ₛS' M q 

-- suc relation is reflexive

suc-state-refl : {τ : Time} → {S : 𝕊 τ} → S ≤ₛ S
suc-state-refl = id-suc

-- suc relation is transitive

suc-state-trans : { τ τ' τ'' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → {S'' : 𝕊 τ''} → 
            S ≤ₛ S' → S' ≤ₛ S'' → S ≤ₛ S''
suc-state-trans id-suc S'≤ₛS'' = S'≤ₛS''
suc-state-trans (⟨⟩-suc p τ'' S≤ₛS') id-suc = ⟨⟩-suc p τ'' S≤ₛS'
suc-state-trans (⟨⟩-suc p τ'' S≤ₛS') (⟨⟩-suc p₁ τ''' S'≤ₛS'') = 
    ⟨⟩-suc (≤-trans p (≤-trans (≤-stepsʳ τ'' ≤-refl) p₁)) τ''' (suc-state-trans (⟨⟩-suc p τ'' S≤ₛS') S'≤ₛS'')
suc-state-trans (⟨⟩-suc p τ'' S≤ₛS') (∷-suc p₁ τ''' V S'≤ₛS'') = 
    ∷-suc (≤-trans p (≤-trans (≤-stepsʳ τ'' ≤-refl) p₁)) τ''' V (suc-state-trans (⟨⟩-suc p τ'' S≤ₛS') S'≤ₛS'')
suc-state-trans (∷-suc p τ'' V S≤ₛS') id-suc = ∷-suc p τ'' V S≤ₛS'
suc-state-trans (∷-suc p τ'' V S≤ₛS') (⟨⟩-suc p₁ τ''' S'≤ₛS'') = 
    ⟨⟩-suc (≤-trans p p₁) τ''' (suc-state-trans (∷-suc p τ'' V S≤ₛS') S'≤ₛS'')
suc-state-trans (∷-suc p τ'' V S≤ₛS') (∷-suc p₁ τ''' V₁ S'≤ₛS'') = 
    ∷-suc (≤-trans p p₁) τ''' V₁ (suc-state-trans (∷-suc (≤-trans ≤-refl p) τ'' V S≤ₛS') S'≤ₛS'')

-- if states are suc of one another they must have equal time

aux-suc-state-antisym : { τ τ' : Time} → {S : 𝕊 τ} → {S' : 𝕊 τ'} → 
            S ≤ₛ S' → S' ≤ₛ S → τ' ≡ τ
aux-suc-state-antisym id-suc sucS'S = refl
aux-suc-state-antisym (⟨⟩-suc p τ'' S≤ₛS') id-suc = refl
aux-suc-state-antisym (⟨⟩-suc p τ'' S≤ₛS') (⟨⟩-suc p₁ τ''' sucS'S) = 
    a≤b⇒b≤a⇒a≡b (≤-trans p₁ (≤-stepsʳ τ''' ≤-refl)) (≤-trans p (≤-stepsʳ τ'' ≤-refl))
aux-suc-state-antisym (⟨⟩-suc p τ'' S≤ₛS') (∷-suc p₁ τ''' V sucS'S) = 
    a≤b⇒b≤a⇒a≡b p₁ (≤-trans p (≤-stepsʳ τ'' ≤-refl))
aux-suc-state-antisym (∷-suc p τ'' V S≤ₛS') id-suc = refl
aux-suc-state-antisym (∷-suc p τ'' V S≤ₛS') (⟨⟩-suc p₁ τ''' sucS'S) = 
    a≤b⇒b≤a⇒a≡b (≤-trans p₁ (≤-stepsʳ τ''' ≤-refl)) p
aux-suc-state-antisym (∷-suc p τ'' V S≤ₛS') (∷-suc p₁ τ''' V₁ sucS'S) = a≤b⇒b≤a⇒a≡b p₁ p

-- operations on state - just for better readability in perservation theorem

time-pass : ∀ {τ} → (S : 𝕊 τ) → (τ' : Time) → 𝕊 (τ + τ')
time-pass S τ = S ⟨ τ ⟩ₘ 

extend-state : ∀ {τ A} → (S : 𝕊 τ) → (τ' : Time) → (V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A) → 𝕊 τ
extend-state S τ' V = S ∷ₘ[ τ' ] V 

-- Lemmas about what can and what can't be in toCtx S (only var can be)

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

var-in-ctx : ∀ { Γ τ' A} → 
            (V : Γ ⊢V⦂ [ τ' ] A) → 
            Σ[ τ'' ∈ Time ] ([ τ' ] A ∈[ τ'' ] Γ )
var-in-ctx (var {τ = τ} x) = τ , x

---------------------------------------
--  resource-lookup related lemmas   --
---------------------------------------

-- general resource-lookup lemma

resource-lookup : ∀ {τ τ' τ'' A} → (S : 𝕊 τ) →
                (x : [ τ' ] A ∈[ τ'' ] toCtx S) →
                (toCtx S -ᶜ τ'') ⟨ τ' ⟩ ⊢V⦂ A
resource-lookup (S ⟨ τ'' ⟩ₘ) (Tl-⟨⟩ {τ' = τ'} x) = 
    V-rename (cong-⟨⟩-ren (η-⟨⟩--ᶜ-ren τ' τ'')) (resource-lookup S x)
resource-lookup (S ∷ₘ[ τ' ] V) Hd = V-rename (cong-⟨⟩-ren wk-ren) V
resource-lookup (S ∷ₘ[ τ' ] V) (Tl-∷ {τ = τ} x) = 
    V-rename (cong-⟨⟩-ren (wk-ren -ʳ τ)) (resource-lookup S x)

-- renaming of the result of previous lemma to context S

resource-pass-to-ctx : ∀ {τ τ' τ'' A} → (S : 𝕊 τ) → 
            (p : τ' ≤ τ'') → 
            (q : τ'' ≤ τ) → 
            (V : (toCtx S -ᶜ τ'') ⟨ τ' ⟩ ⊢V⦂ A) → 
            toCtx S ⊢V⦂ A
resource-pass-to-ctx S p q V = V-rename (wk-⟨⟩--ᶜ-ren p (τ-≤-substᵣ (ctx-timeSτ≡τ S) q)) V

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
from-head-time-positive {Γ = Γ ⟨ τ' ⟩} {τ = .(τ' + τ'')} (Tl-⟨⟩ {τ = τ'} {τ''} x) = 
    τ-≤-substᵣ (sym (+-comm τ' (ctx-time Γ))) (≤-extend τ' τ'' (ctx-time Γ) (from-head-time-positive x))

 