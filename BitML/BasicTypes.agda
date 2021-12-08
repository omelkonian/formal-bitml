------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------
module BitML.BasicTypes where

open import Prelude.Init

Value  = ℕ
Values = List Value

Secret  = String
Secrets = List Secret

Id  = String
Ids = List String

Name : Set
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
