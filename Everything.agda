------------------------------------------------------------------------
-- Agda formalisation of the syntax and semantics of a core language  --
-- for programming with temporal resources using modal types.         --
--                                                                    --
-- The language has:                                                  --
--                                                                    --
--   - a modality on types that specifies that data might not yet be  --
--     available, but is guaranteed to be in at most τ time steps     --
--                                                                    --
--   - a modality on contexts describing that at least τ time steps   --
--     have passed (allowing new data to become available)            --
--                                                                    --
--   - features facilitating the interaction of these two modalities  --
--     based on adjunctions (i.e., Fitch-style modal type systems)    --
--                                                                    --
--   - computational effects modelled using algebraic operations with --
--     prescribed execution times and whose execution makes time pass --
--     (both in the semantics and also in the static typing rules)    --
--                                                                    --
--   - semantics in time-varying sets (covariant presheaves on (ℕ,≤)) --
--                                                                    --
------------------------------------------------------------------------

module Everything where


-- UTILS
--------

---- Equality

open import Util.Equality

---- Time

open import Util.Time

---- Algebraic operations

open import Util.Operations


-- SYNTAX
---------

---- Syntax of the language

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

---- Renamings and substitutions

open import Syntax.Renamings
open import Syntax.Substitutions

---- Equational theory

open import Syntax.EquationalTheory


-- SEMANTICS
------------

---- Models

open import Semantics.Model

---- Interpretation of types/terms

open import Semantics.Interpretation

open import Semantics.Interpretation.Properties.split-env-isomorphism
open import Semantics.Interpretation.Properties.split-env-naturality
open import Semantics.Interpretation.Properties.var-in-env-decompose
open import Semantics.Interpretation.Properties.var-in-env-var-rename
open import Semantics.Interpretation.Properties.env-⟨⟩-ᶜ-naturality

---- Semantics of renamings

open import Semantics.Renamings

open import Semantics.Renamings.Properties.-ᶜ-wk-ren-decompose
open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-ren-naturality
open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-split-env-naturality
open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-eq-ren-naturality
open import Semantics.Renamings.Properties.split-env-eq-ren

---- Semantics of substitutions

-- open import Semantics.Substitutions.Properties.VC-subst

open import Semantics.Substitutions.Properties.var-subst


-- TIME-VARYING SETS MODEL
--------------------------

-- open import Semantics.Model.Examples.TSets.Model
