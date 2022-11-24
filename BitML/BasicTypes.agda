------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------
module BitML.BasicTypes where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Sets

Value  = ℕ
Values = Set⟨ Value ⟩

Secret  = String
Secrets = Set⟨ Secret ⟩

Id  = String
Ids = Set⟨ String ⟩

Name = Secret ⊎ Id
Names = Set⟨ Name ⟩

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
