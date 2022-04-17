---------------------------
-- Types of the language --
---------------------------

open import Util.Operations
open import Util.Time

module Syntax.Types where

-- Value and computation types

mutual

  data VType : Set where
    Base  : BaseType → VType                 -- base types
    Unit  : VType                            -- unit type
    Empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    [_]_  : Time → VType → VType             -- temporal modality: values of type `[ t ] A`
                                             -- become available in at most `t` time steps
  data CType : Set where
    _‼_ : VType → Time → CType

  infix  37 [_]_
  infixr 30 _⇒_
  infix  31 _‼_

-- Embedding ground types into types

type-of-gtype : GType → VType
type-of-gtype (Base B) = Base B
type-of-gtype Unit     = Unit
type-of-gtype Empty    = Empty
