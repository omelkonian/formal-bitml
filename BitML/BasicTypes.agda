------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------
module BitML.BasicTypes where

open import Data.Nat    using (ℕ)
open import Data.String using (String)
open import Data.List   using (List)
open import Data.Sum    using (_⊎_)

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

  v v′ : Value
  vs vs′ : Values

  a a′ : Secret
  as as′ : Secrets

  x y z x′ y′ z′ : Id
  xs xs′ : Ids

  t t′ δ : Time
