-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

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
open import Semantics.Renamings.Properties.wk-⟨⟩-ctx
open import Semantics.Renamings.Properties.Rename


open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Renamings where
