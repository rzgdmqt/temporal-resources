-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Semantics.Model

module Semantics.Renamings (Mod : Model) where

open import Semantics.Renamings.Core Mod public

open import Semantics.Renamings.Properties.env-⟨⟩-ᶜ-naturality Mod public   -- TODO: finish typing up
open import Semantics.Renamings.Properties.var-in-env-var-rename Mod public
open import Semantics.Renamings.Properties.VC-rename Mod public

-- Other renamings related lemmas (e.g., decompositions of maps)

-- open import Semantics.Renamings.Properties.var-in-env-decompose Mod   -- TODO: finish typing up
