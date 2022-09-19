-------------------------------------
-- Semantics of variable renamings --
-------------------------------------

open import Semantics.Model

module Semantics.Renamings (Mod : Model) where

open import Semantics.Renamings.Core Mod public

open import Semantics.Renamings.Properties.VC-rename Mod public
