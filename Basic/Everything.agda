--------------------------------------------------------------
-- Agda formalisation of the syntax and semantics of a core --
-- language for programming with modal temporal resources   --
--------------------------------------------------------------

module Everything where

-- UTILS
--------

---- Time

open import Util.Time

---- Algebraic operations

open import Util.Operations


-- LANGUAGE
-----------

---- Syntax of the language

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

open import Semantics.Monad

---- Interpretation

open import Semantics.Interpretation
