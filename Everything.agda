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

---- Propositions as [Types]

open import Util.HProp


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


-- ABSTRACT SEMANTICS
---------------------

---- Models

open import Semantics.Model

---- Interpretation of types/terms

open import Semantics.Interpretation

---- Semantics of renamings

open import Semantics.Renamings


-- TIME-VARYING SETS MODEL
--------------------------

---- Time-varying sets

open import Semantics.Model.Examples.TSets.TSets

---- Semantics of base types

open import Semantics.Model.Examples.TSets.BaseGroundTypes

---- Temporal modalities

open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.Modality.Adjunction

---- Free monad on algebraic operations

open import Semantics.Model.Examples.TSets.Monad

---- Time-varying sets model

open import Semantics.Model.Examples.TSets.Model
