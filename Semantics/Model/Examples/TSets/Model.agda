-------------------------------------------------------
-- Model of the language based on time-varying sets  --
-------------------------------------------------------

module Semantics.Model.Examples.TSets.Model where

open import Semantics.Model

open import Semantics.Model.Examples.TSets.TSets

open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.Modality.Adjunction

open import Semantics.Model.Examples.TSets.BaseGroundTypes

open import Semantics.Model.Examples.TSets.Monad

open import Util.Equality
open import Util.Operations
open import Util.Time

-- The TSet model

TSetModel : Model
TSetModel = record
  { Cat = TSetCat
  ; Fut = TSetFut
  ; Pas = TSetPas
  ; Adj = TSetAdj
  ; Typ = TSetTyp
  ; Mon = TSetMon
  }
