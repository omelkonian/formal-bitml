------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------
module BitML.BasicTypes where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq

Value  = ℕ
Values = List Value

Secret  = String
Secrets = List Secret

Id  = String
Ids = List String

Name = Secret ⊎ Id
Names = List Name

Time = ℕ

variable
  n : ℕ

  v v′ v″ : Value
  vs vs′ vs″ : Values

  a a′ a″ : Secret
  as as′ as″ : Secrets

  x y z x′ y′ z′ x″ y″ z″ : Id
  xs xs′ xs″ : Ids

  t δ t′ δ′ t″ δ″ : Time

-- module parameters

record ⋯ : Type₁ where
  constructor ⋯_,_⋯
  field Participant    : Type
        ⦃ decEq-part ⦄ : DecEq Participant
        Honest         : List⁺ Participant
  Hon = L.NE.toList Honest
