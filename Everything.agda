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
--   - denotational semantics based on adjunctions between strong     --
--     monoidal functors, and on strong graded monads                 --
--                                                                    --
--   - concrete semantics example using covariant presheaves on (ℕ,≤) --
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

---- Interpretation of types and terms

open import Semantics.Interpretation

open import Semantics.Interpretation.Properties.var-in-env-decompose

---- Semantics of renamings

open import Semantics.Renamings

open import Semantics.Renamings.Properties.VC-rename

---- Semantics of substitutions

open import Semantics.Substitutions.Properties.VC-subst

---- Soundness of the interpretation

open import Semantics.Soundness


-- PRESHEAF MODEL
-----------------

open import Semantics.Model.Example.TSets.Monad.Core
open import Semantics.Model.Example.TSets.Monad.Effects
open import Semantics.Model.Example.TSets.Monad.Effects.Properties.Algebraicity
open import Semantics.Model.Example.TSets.Monad.Effects.Properties.Naturality
open import Semantics.Model.Example.TSets.Monad.Strength
open import Semantics.Model.Example.TSets.Monad.Strength.Properties.Algebraicity
open import Semantics.Model.Example.TSets.Monad.Strength.Properties.Naturality
open import Semantics.Model.Example.TSets.Monad.Strength.Properties.UnitMultiplication
open import Semantics.Model.Example.TSets.Monad.Strength.Properties.CartesianStructure
open import Semantics.Model.Example.TSets.Monad.Handling
open import Semantics.Model.Example.TSets.Monad.Handling.Properties.Unit
open import Semantics.Model.Example.TSets.Monad.Handling.Properties.Delay

-- TODO: commented out because extremely slow typechecking (see README)

-- open import Semantics.Model.Example.TSets.Monad
-- open import Semantics.Model.Examples.TSets.Model 
