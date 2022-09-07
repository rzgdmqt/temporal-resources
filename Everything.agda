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


-- SEMANTICS
------------

---- Time-varying sets

open import Semantics.TSets

---- Temporal modalities

open import Semantics.Modality.Future
open import Semantics.Modality.Past

---- Adjunction between modalities

open import Semantics.Modality.Adjunction

---- Free monad on algebraic operations

open import Semantics.Monad.Core

open import Semantics.Monad.Strength
open import Semantics.Monad.Strength.Naturality
open import Semantics.Monad.Strength.Algebraicity

open import Semantics.Monad.Effects
open import Semantics.Monad.Effects.Naturality
open import Semantics.Monad.Effects.Algebraicity

open import Semantics.Monad.Handling

open import Semantics.Monad

---- Interpretation of types and terms

open import Semantics.Interpretation

---- Semantics of renamings

open import Semantics.Renamings.Core
open import Semantics.Renamings.Properties.Rename
open import Semantics.Renamings
