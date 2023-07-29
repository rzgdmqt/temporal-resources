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
------------------------------------------------------------------------

module MasterThesis where

-- UTILS
--------

---- Equality

open import Util.Equality

---- Time

open import Util.Time

---- Algebraic operations

open import Util.Operations

---- Properties - mostly equalities between natural numbers

open import Util.Properties


-- SYNTAX
---------

---- Syntax of the language

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

---- Renamings and substitutions

open import Syntax.Renamings
open import Syntax.Substitutions

---- State

open import Syntax.State

---- Small-steps operational semantics and perservation theorem 

open import Syntax.PerservationTheorem

---- Some usefull theorems about step relation 

open import Syntax.TheoremsAboutSteps

---- Progress theorem

open import Syntax.ProgressTheorem

----Computational contexts

open import Syntax.CompContext

---- Equational theory

open import Syntax.EquationalTheory

---- Soundness theorem

open import Syntax.Soundness