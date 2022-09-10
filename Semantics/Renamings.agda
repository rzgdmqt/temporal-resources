-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

module Semantics.Renamings where

open import Function

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings

open import Semantics.TSets
open import Semantics.Modality.Past
open import Semantics.Interpretation
open import Semantics.Renamings.Core
open import Semantics.Renamings.Properties.VC-rename

open import Util.Equality
open import Util.Operations
open import Util.Time
