----------------------------
-- Model for the language --
----------------------------

module Semantics.Model where

open import Semantics.Model.Category

open import Semantics.Model.Modality.Future
open import Semantics.Model.Modality.Past
open import Semantics.Model.Modality.Adjunction

open import Semantics.Model.BaseGroundTypes

open import Semantics.Model.Monad

open import Util.Equality
open import Util.Operations
open import Util.Time

record Model : Set₂ where

  field

    -- Category

    Cat : Category

    -- Modalities

    Fut : Future Cat
    Pas : Past Cat
    Adj : Adjunction Cat Fut Pas

    -- Semantics of base and ground types

    Typ : BaseGroundTypes Cat Fut

    -- Monad

    Mon : Monad Cat Fut Typ

  -- Opening all the structure for public usage

  open Category Cat public
  open import Semantics.Model.Category.Derived Cat public

  open Future Fut public
  open Past Pas public
  open Adjunction Adj public

  open BaseGroundTypes Typ public

  open Monad Mon public
