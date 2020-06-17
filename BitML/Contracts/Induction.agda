{-# OPTIONS --postfix-projections #-}
open import Level    using (0ℓ)
open import Function using (_∘_; _$_; _on_)

open import Induction
open import Induction.WellFounded
open import Data.Nat.Induction using (<-wellFounded)

open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat

open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality
  hiding ([_])

open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Measurable

module BitML.Contracts.Induction
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts.Types Participant Honest
open import BitML.Contracts.Helpers Participant Honest

ℂ : Set
ℂ = Contract ⊎ Contracts ⊎ VContracts

∣_∣ᶜ : Contract → ℕ

instance
  {-# TERMINATING #-}
  Measurableᶜ : Measurable Contract
  Measurableᶜ .∣_∣ = ∣_∣ᶜ

  MeasurableV : Measurable (Value × Contracts)
  MeasurableV .∣_∣ (_ , c) = ∣ c ∣

∣ put _ &reveal _ if _ ⇒ cs ∣ᶜ = suc ∣ cs ∣
∣ withdraw _                ∣ᶜ = 1
∣ split vcs                 ∣ᶜ = suc ∣ vcs ∣
∣ _ ⇒ c                     ∣ᶜ = suc ∣ c ∣ᶜ
∣ after _ ⇒ c               ∣ᶜ = suc ∣ c ∣ᶜ

private
  _ : Contract → ℕ
  _ = ∣_∣

  _ : Contracts → ℕ
  _ = ∣_∣

  _ : VContracts → ℕ
  _ = ∣_∣

  _ : ℂ → ℕ
  _ = ∣_∣
