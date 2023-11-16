module OperationalSemantics.StateCtx where

open import Syntax.Contexts
open import Syntax.CompContext
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Types

open import Data.Empty
open import Util.Equality
open import Data.Product
open import Util.Time

-- Definition of state

mutual
  data 𝕊 (Γ : Ctx) : Set where
    ∅     : 𝕊 Γ
    _⟨_⟩ₛ : 𝕊 Γ → (τ : Time) → 𝕊 Γ  
    _∷ₛ_  : ∀ {A τ} → (S : 𝕊 Γ) → ((Γ ++ᶜ (toCtx S) ⟨ τ ⟩) ⊢V⦂ A) → 𝕊 Γ

  toCtx : ∀ {Γ} → 𝕊 Γ → Ctx
  toCtx ∅ = []
  toCtx (S ⟨ τ ⟩ₛ) = (toCtx S) ⟨ τ ⟩
  toCtx (_∷ₛ_ {A = A} {τ = τ} S V) = (toCtx S ∷ [ τ ] A)

  infixl 31 _∷ₛ_
  infix  32 _⟨_⟩ₛ


-- operations on state - just for better readability in perservation theorem

time-pass : ∀ {Γ} → (S : 𝕊 Γ) → (τ' : Time) → 𝕊 Γ
time-pass S τ = S ⟨ τ ⟩ₛ 

extend-state : ∀ {Γ A τ} → (S : 𝕊 Γ) → ((Γ ++ᶜ (toCtx S) ⟨ τ ⟩) ⊢V⦂ A) → 𝕊 Γ
extend-state S V = S ∷ₛ V 

-- Sum of time passing in the state

state-time : ∀ {Γ} → (S : 𝕊 Γ) → Time
state-time ∅ = 0
state-time (S ⟨ τ ⟩ₛ) = state-time S + τ
state-time (S ∷ₛ A) = state-time S

-- State time is the same as context time of toCtx S 

time-≡ : ∀ {Γ} → (S : 𝕊 Γ) → state-time S ≡ ctx-time (toCtx S)
time-≡ ∅ = refl
time-≡ (S ⟨ τ ⟩ₛ) = cong (_+ τ) (time-≡ S)
time-≡ (S ∷ₛ A) = time-≡ S

-- Definition of successor of a state

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
            → S ≤ₛ (S' ⟨ τ'' ⟩ₛ)

    ∷-suc : ∀ {Γ Γ' τ A} 
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (V : (Γ' ++ᶜ (toCtx S') ⟨ τ ⟩) ⊢V⦂ A) 
            → S ≤ₛ S' 
            ----------------
            → S ≤ₛ (S' ∷ₛ V)

-- if two states are successors they can be renamed contexts

≤ₛ⇒Ren : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → Ren (toCtx S) (toCtx S')
≤ₛ⇒Ren id-suc = id-ren
≤ₛ⇒Ren (⟨⟩-suc τ'' y) = wk-⟨⟩-ren ∘ʳ (≤ₛ⇒Ren y)
≤ₛ⇒Ren (∷-suc V y) = wk-ren ∘ʳ (≤ₛ⇒Ren y)

-- ≤ₛ increase time

S≤ₛS'⇒τ≤τ' : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → (state-time S) ≤ (state-time S')
S≤ₛS'⇒τ≤τ' {S = S} {S' = .S} id-suc = ≤-refl
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ⟨ τ'' ⟩ₛ)} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') = 
    ≤-stepsʳ τ'' 
        (τ-≤-substᵣ (time-≡ S')
        (τ-≤-substₗ (sym (time-≡ S)) 
    (Ren.ctx-time-≤ (≤ₛ⇒Ren S≤ₛS'))))
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ∷ₛ V)} (∷-suc {S' = S'} V S≤ₛS') = 
    τ-≤-substᵣ (time-≡ S') 
    (τ-≤-substₗ (sym (time-≡ S)) 
    (Ren.ctx-time-≤ (≤ₛ⇒Ren S≤ₛS')))


-- Lemma if one state is successor of another and overall time inreases we 
-- can rename it

suc-comp-ren : ∀ {Γ Γ'} 
        → { τ'' τ''' : Time} 
        → {S : 𝕊 Γ} 
        → {S' : 𝕊 Γ'} 
        → S ≤ₛ S' 
        → (q : state-time S + τ'' ≤ state-time S' + τ''') 
        → Ren (toCtx S ⟨ τ'' ⟩) (toCtx S' ⟨ τ''' ⟩)
suc-comp-ren {S = S} id-suc q = 
  ⟨⟩-≤-ren (+-cancelˡ-≤ (state-time S) q)
suc-comp-ren {τ'' = τ} {τ'''} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') q = 
  ⟨⟩-μ-ren 
    ∘ʳ suc-comp-ren S≤ₛS' (τ-≤-substᵣ (sym (+-assoc (state-time S') τ'' τ''')) q)
suc-comp-ren {S = S} (∷-suc V S≤ₛS') q = 
  (cong-⟨⟩-ren wk-ren) 
    ∘ʳ suc-comp-ren S≤ₛS' q

-- Concatenation/composition of states

mutual
  _++ˢ_ : ∀ {Γ} → (S : 𝕊 Γ) → (𝕊 (Γ ++ᶜ toCtx S)) → 𝕊 Γ
  S ++ˢ ∅ =
    S
  S ++ˢ (S' ⟨ τ ⟩ₛ) =
    (S ++ˢ S') ⟨ τ ⟩ₛ
  _++ˢ_ {Γ} S (_∷ₛ_ {τ = τ} S' V) =
    (S ++ˢ S') ∷ₛ
      V-rename (eq-ren (cong (_⟨ τ ⟩)
                       (trans (++ᶜ-assoc Γ (toCtx S) (toCtx S'))
                       (cong (Γ ++ᶜ_) (sym (toCtx-++ˢ S S'))))))
               V

  infixl 30 _++ˢ_

  toCtx-++ˢ : ∀ {Γ}
            → (S : 𝕊 Γ)
            → (S' : 𝕊 (Γ ++ᶜ toCtx S))
            → toCtx (S ++ˢ S') ≡ toCtx S ++ᶜ toCtx S'
   
  toCtx-++ˢ S ∅ =
    refl
  toCtx-++ˢ S (S' ⟨ τ ⟩ₛ) =
    cong (_⟨ τ ⟩) (toCtx-++ˢ S S')
  toCtx-++ˢ S (_∷ₛ_ {A = A} {τ = τ} S' V) =
    cong (_∷ [ τ ] A) (toCtx-++ˢ S S')

-- Splitting a state according to a variable/resource in it

mutual 

  split-state-fst : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → [ τ ] A ∈[ τ' ] (toCtx S)
                  → 𝕊 Γ
   
  split-state-fst (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-fst S x
  split-state-fst (S ∷ₛ V) Hd =
    S
  split-state-fst (S ∷ₛ V) (Tl-∷ x) =
    split-state-fst S x
   
  split-state-snd : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → 𝕊 (Γ ++ᶜ toCtx (split-state-fst S x) ∷ [ τ ] A)
  
  split-state-snd (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-snd S x ⟨ τ ⟩ₛ
  split-state-snd (S ∷ₛ V) Hd =
    ∅
  split-state-snd {Γ} (_∷ₛ_ {τ = τ} S V) (Tl-∷ x) =
    split-state-snd S x ∷ₛ
    V-rename (eq-ren (cong (_⟨ τ ⟩)
      (trans
        (sym (cong (Γ ++ᶜ_) (split-state-++ᶜ S x)))
        (sym (++ᶜ-assoc Γ _ (toCtx (split-state-snd S x)))))))
    V

  split-state-++ᶜ : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → toCtx (split-state-fst S x) ∷ [ τ ] A ++ᶜ toCtx (split-state-snd S x) ≡ toCtx S

  split-state-++ᶜ (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) =
    cong (_⟨ τ ⟩) (split-state-++ᶜ S x)
  split-state-++ᶜ (_∷ₛ_ {A = A} {τ = τ} S V) Hd =
    refl
  split-state-++ᶜ (_∷ₛ_ {A = A} {τ = τ} S V) (Tl-∷ x) =
    cong (_∷ [ τ ] A) (split-state-++ᶜ S x)

fst-split-state≡split-ctx : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → toCtx (split-state-fst S x) ≡ proj₁ (var-split x)
fst-split-state≡split-ctx (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) = fst-split-state≡split-ctx S x
fst-split-state≡split-ctx (S ∷ₛ V) Hd = refl
fst-split-state≡split-ctx (S ∷ₛ V) (Tl-∷ x) = fst-split-state≡split-ctx S x

split-state≡split-ctx : ∀ {Γ A τ τ'}
                  → {S : 𝕊 Γ}
                  → {x : [ τ ] A ∈[ τ' ] (toCtx S)}
                  → toCtx (split-state-fst S x) ∷ [ τ ] A ++ᶜ (toCtx (split-state-snd S x))  
                  ≡ 
                  proj₁ (var-split x) ∷ [ τ ] A ++ᶜ (proj₁ (proj₂ (var-split x)))
split-state≡split-ctx {S = S} {x = x} = 
        trans (split-state-++ᶜ S x) 
            (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))

cons-inj : ∀ {Γ Γ' A} → A ∷ₗ Γ ≡ A ∷ₗ Γ' → Γ ≡ Γ' 
cons-inj refl = refl

time-pass-inj : ∀ {Γ Γ' τ} → ⟨ τ ⟩ₗ Γ ≡ ⟨ τ ⟩ₗ Γ' → Γ ≡ Γ' 
time-pass-inj refl = refl

Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' : ∀ {Δ₁ Δ₁' Δ₂ Δ₂'} → Δ₁ ≡ Δ₂ → Δ₁ ++ₗ Δ₁' ≡ Δ₂ ++ₗ Δ₂' → Δ₁' ≡ Δ₂'
Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' {[]ₗ} refl q = q
Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' {x ∷ₗ Δ₁} refl q = Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' {Δ₁ = Δ₁} refl (cons-inj q)
Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' {⟨ τ ⟩ₗ Δ₁} refl q = Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' {Δ₁ = Δ₁} refl (time-pass-inj q)

Ctx≡BCtx : ∀ {Γ Γ'} → Ctx→Bctx Γ ≡ Ctx→Bctx Γ' → Γ ≡ Γ'
Ctx≡BCtx {Γ} {Γ'} p =
  trans
    (sym (Ctx→Bctx→Ctx-iso Γ))
    (trans
      (cong BCtx→Ctx p)
      (Ctx→Bctx→Ctx-iso Γ'))

Γ₁≡Γ₂⇒Γ₁++Γ₁'≡Γ₂++Γ₂'⇒Γ₁'≡Γ₂' : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → Γ₁ ≡ Γ₂ → Γ₁ ++ᶜ Γ₁' ≡ Γ₂ ++ᶜ Γ₂' → Γ₁' ≡ Γ₂'
Γ₁≡Γ₂⇒Γ₁++Γ₁'≡Γ₂++Γ₂'⇒Γ₁'≡Γ₂' {Γ₁} {Γ₁'} {.Γ₁} {Γ₂'} refl q =
   Ctx≡BCtx (Δ₁≡Δ₂⇒Δ₁++Δ₁'≡Δ₂++Δ₂'⇒Δ₁'≡Δ₂' 
       {Δ₁ = Ctx→Bctx Γ₁} 
           refl 
           (trans (Ctx→Bctx-hom Γ₁ Γ₁') 
               (trans (cong Ctx→Bctx q) 
                   (sym (Ctx→Bctx-hom Γ₁ Γ₂')))))


snd-split-state≡split-ctx : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → toCtx (split-state-snd S x) ≡ proj₁ (proj₂ (var-split x))
snd-split-state≡split-ctx {A = A} {τ = τ} S x = 
    Γ₁≡Γ₂⇒Γ₁++Γ₁'≡Γ₂++Γ₂'⇒Γ₁'≡Γ₂' 
        (cong (_∷ [ τ ] A) (fst-split-state≡split-ctx S x)) 
        split-state≡split-ctx

snd-split-time≡time-from-head : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → state-time (split-state-snd S x) ≡ τ'
snd-split-time≡time-from-head S x = 
  trans (
    trans 
      (time-≡ (split-state-snd S x)) 
      (cong ctx-time (snd-split-state≡split-ctx S x))) 
    (proj₂ (proj₂ (proj₂ (var-split x))))

-- Lemmas about what can and what can't be in toCtx S (only var can be)

⇒-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A : VType} {C : CType} → A ⇒ C ∈[ τ ] toCtx S → ⊥
⇒-not-in-toCtx {S = S ⟨ τ ⟩ₛ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A B : VType} → A |×| B ∈[ τ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ τ'' ⟩ₛ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} → Empty ∈[ τ ] toCtx S → ⊥
Empty-not-in-toCtx {S = S ⟨ τ'' ⟩ₛ} (Tl-⟨⟩ x) = Empty-not-in-toCtx x
Empty-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Empty-not-in-toCtx x

not-in-empty-ctx : {τ : Time} {A : VType} → A ∈[ τ ] [] → ⊥
not-in-empty-ctx ()

var-in-ctx : ∀ { Γ τ' A} → 
            (V : Γ ⊢V⦂ [ τ' ] A) → 
            Σ[ τ'' ∈ Time ] ([ τ' ] A ∈[ τ'' ] Γ )
var-in-ctx (var {τ = τ} x) = τ , x


τ'≤snd-state : ∀ {A τ'} 
        → {S : 𝕊 []}
        → (V : toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)
        → τ' ≤
    state-time (split-state-snd S (var-ᶜ-+ {τ = τ'} (proj₂ (var-in-ctx V))))
τ'≤snd-state {τ' = τ'} {S = S} (var {τ = τ} x) = 
  let y = var-ᶜ-+ {τ = τ'} x in 
  τ-≤-substᵣ (snd-split-time≡time-from-head S y) (≤-stepsˡ τ ≤-refl)


-- Looking up a resource in the state

resource-lookup : ∀ {Γ τ τ' A}
                → (S : 𝕊 Γ)
                → (x : [ τ ] A ∈[ τ' ] toCtx S)
                → (Γ ++ᶜ toCtx (split-state-fst S x)) ⟨ τ ⟩ ⊢V⦂ A
resource-lookup (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ {τ' = τ'} x) =
  resource-lookup S x
resource-lookup (S ∷ₛ V) Hd =
  V
resource-lookup (S ∷ₛ V) (Tl-∷ {τ = τ} x) =
  resource-lookup S x

-- Renaming of the result of previous lemma to context for state S

resource-pass-to-ctx : ∀ {Γ τ τ' A}
                     → (S : 𝕊 Γ)
                     → (x : [ τ ] A ∈[ τ' ] toCtx S)
                     → (p : τ ≤ ctx-time (toCtx (split-state-snd S x)))
                     → (V : (Γ ++ᶜ toCtx (split-state-fst S x)) ⟨ τ ⟩ ⊢V⦂ A)
                     → Γ ++ᶜ toCtx S ⊢V⦂ A
resource-pass-to-ctx {Γ} {τ} {τ'} {A} S x p V =
  V-rename
    (   eq-ren (cong (Γ ++ᶜ_) (split-state-++ᶜ S x)) 
     ∘ʳ eq-ren (++ᶜ-assoc Γ (toCtx (split-state-fst S x) ∷ [ τ ] A) (toCtx (split-state-snd S x))) 
     ∘ʳ cong-ren wk-ren
     ∘ʳ ren⟨τ⟩-ctx {Γ' = toCtx (split-state-snd S x)} p)
    V


-- Translating states to computation term contexts

toK : ∀ {Γ A τ}
    → (S : 𝕊 Γ)
    → Γ ⊢K[ state ◁ Ctx→Bctx (toCtx S) ⊢ A ‼ τ ]⦂ (A ‼ (ctx-time (toCtx S) + τ))
    
toK ∅ =
  []ₖ
toK {A = A} {τ = τ'} (S ⟨ τ ⟩ₛ) =
  (τ-substK (sym (+-assoc _ τ τ')) (toK {A = A} {τ = τ + τ' } S)) [ delay[ f≤ᶠf ]ₖ τ []ₖ ]ₖ
toK (_∷ₛ_ {τ = τ} S V) =
  (toK S) [ box[ f≤ᶠf ]ₖ (V-rename (eq-ren (cong (_⟨ τ ⟩) (sym (⋈-++ₗ-[] _ (toCtx S))))) V) []ₖ ]ₖ









-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------


{-

-- lemma that context from state is equal to context from state context

Γ≡toCtxS : ∀ {Γ} → (S : 𝕊 Γ) → Γ ≡ toCtx S
Γ≡toCtxS ∅ = refl
Γ≡toCtxS (S ⟨ τ ⟩ₛ) = cong (_⟨ τ ⟩) (Γ≡toCtxS S)
Γ≡toCtxS (_∷ₛ_ {A = A₁} {τ = τ} S A) = cong (_∷ [ τ ] A₁) (Γ≡toCtxS S)

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
            → S ≤ₛ (S' ⟨ τ'' ⟩ₛ)

    ∷-suc : ∀ {Γ Γ' τ A} 
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (V : (Γ' ⟨ τ ⟩) ⊢V⦂ A) 
            → S ≤ₛ S' 
            ----------------
            → S ≤ₛ (S' ∷ₛ V)

state-time : ∀ {Γ} → (S : 𝕊 Γ) → Time
state-time ∅ = 0
state-time (S ⟨ τ ⟩ₛ) = state-time S + τ
state-time (S ∷ₛ A) = state-time S

-- lemma that ctx-time of toCtx S is the same as state-time S

ctx-time≡state-time : ∀ {Γ} → (S : 𝕊 Γ) → ctx-time (toCtx S) ≡ (state-time S)
ctx-time≡state-time ∅ = refl 
ctx-time≡state-time (S ⟨ τ ⟩ₛ) = cong (_+ τ) (ctx-time≡state-time S)
ctx-time≡state-time (S ∷ₛ A) = ctx-time≡state-time S

-- if two states are successors they can be renamed contexts

≤ₛ⇒Ren : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → Ren (toCtx S) (toCtx S')
≤ₛ⇒Ren id-suc = id-ren
≤ₛ⇒Ren (⟨⟩-suc τ'' y) = wk-⟨⟩-ren ∘ʳ (≤ₛ⇒Ren y)
≤ₛ⇒Ren (∷-suc V y) = wk-ren ∘ʳ (≤ₛ⇒Ren y)

-- ≤ₛ increase time

S≤ₛS'⇒τ≤τ' : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → (state-time S) ≤ (state-time S')
S≤ₛS'⇒τ≤τ' {S = S} {S' = .S} id-suc = ≤-refl
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ⟨ τ'' ⟩ₛ)} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') = 
    ≤-stepsʳ τ'' 
        (τ-≤-substᵣ (sym (ctx-time≡state-time S')) 
        (τ-≤-substₗ (ctx-time≡state-time S) 
    (ren-≤-ctx-time (≤ₛ⇒Ren S≤ₛS'))))
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ∷ₛ V)} (∷-suc {S' = S'} V S≤ₛS') = 
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
time-pass S τ = S ⟨ τ ⟩ₛ 

extend-state : ∀ {Γ A τ'} → (S : 𝕊 Γ) → (Γ ⟨ τ' ⟩ ⊢V⦂ A) → 𝕊 (Γ ∷ ([ τ' ] A))
extend-state S V = S ∷ₛ V 

-- Lemmas about what can and what can't be in toCtx S (only var can be)

⇒-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A : VType} {C : CType} → A ⇒ C ∈[ τ ] toCtx S → ⊥
⇒-not-in-toCtx {S = S ⟨ τ ⟩ₛ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A B : VType} → A |×| B ∈[ τ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ τ'' ⟩ₛ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} → Empty ∈[ τ ] toCtx S → ⊥
Empty-not-in-toCtx {S = S ⟨ τ'' ⟩ₛ} (Tl-⟨⟩ x) = Empty-not-in-toCtx x
Empty-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Empty-not-in-toCtx x

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
resource-lookup (S ⟨ τ'' ⟩ₛ) (Tl-⟨⟩ {τ' = τ'} x) = 
    V-rename (cong-⟨⟩-ren (η-⟨⟩--ᶜ-ren τ' τ'')) (resource-lookup S x)
resource-lookup (_∷ₛ_ {τ = τ} S V) Hd = 
    V-rename (cong-⟨⟩-ren wk-ren) (V-rename (eq-ren (Γ≡toCtxS (S ⟨ τ ⟩ₛ))) V)
resource-lookup (S ∷ₛ V) (Tl-∷ {τ = τ} x) = 
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
                → Γ ⊢ S , Γ' ∷ [ τ ] A ⊢ S' ∷ₛ V SSplit Γ'' ∷ [ τ ] A ⊢ (S'' ∷ₛ V-rename (cong-⟨⟩-ren ρ) V)

    SSplit-⟨⟩  : ∀ {Γ Γ' Γ'' τ}
                → {S : 𝕊 Γ}  
                → {S' : 𝕊 Γ'}  
                → {S'' : 𝕊 Γ''}  
                → Γ ⊢ S , Γ' ⊢ S' SSplit Γ'' ⊢ S'' 
                --------------------------------------------------------------
                → Γ ⊢ S , Γ' ⟨ τ ⟩ ⊢ S' ⟨ τ ⟩ₛ SSplit Γ'' ⟨ τ ⟩ ⊢ (S'' ⟨ τ ⟩ₛ)

_++ₛ_ : ∀ {Γ Γ'} → (S : 𝕊 Γ) → (S' : 𝕊 Γ') → 𝕊 (Γ ++ᶜ Γ')
S ++ₛ ∅ = S
S ++ₛ (S' ⟨ τ ⟩ₛ) = (S ++ₛ S') ⟨ τ ⟩ₛ
S ++ₛ (S' ∷ₛ V) = (S ++ₛ S') ∷ₛ V-rename (cong-⟨⟩-ren (cong-ren {Γ = []} empty-ren ∘ʳ eq-ren (sym ++ᶜ-identityˡ))) V

 
-}
 
