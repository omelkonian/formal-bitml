------------------------------------------------------------------------
-- Decidable equality for predicates.
------------------------------------------------------------------------
module BitML.Predicate.DecidableEquality where

open import Data.Integer using (ℤ)
  renaming (_≟_ to _≟ℤ_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import BitML.BasicTypes
open import BitML.Predicate.Base

import Prelude.Set' as SET

_≟ᵃʳ_ : Decidable {A = Arith} _≡_
` x ≟ᵃʳ ` x₁
  with x ≟ℤ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
` x ≟ᵃʳ ∣ x₁ ∣ = no (λ ())
` x ≟ᵃʳ (y `+ y₁) = no (λ ())
` x ≟ᵃʳ (y `- y₁) = no (λ ())

∣ x ∣ ≟ᵃʳ ` x₁ = no (λ ())
∣ x ∣ ≟ᵃʳ ∣ x₁ ∣
  with x ≟ₛ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
∣ x ∣ ≟ᵃʳ (y `+ y₁) = no (λ ())
∣ x ∣ ≟ᵃʳ (y `- y₁) = no (λ ())

(x `+ x₁) ≟ᵃʳ ` x₂ = no (λ ())
(x `+ x₁) ≟ᵃʳ ∣ x₂ ∣ = no (λ ())
(x `+ x₁) ≟ᵃʳ (y `+ y₁)
  with x ≟ᵃʳ y
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᵃʳ y₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x `+ x₁) ≟ᵃʳ (y `- y₁) = no (λ ())

(x `- x₁) ≟ᵃʳ ` x₂ = no (λ ())
(x `- x₁) ≟ᵃʳ ∣ x₂ ∣ = no (λ ())
(x `- x₁) ≟ᵃʳ (y `+ y₁) = no (λ ())
(x `- x₁) ≟ᵃʳ (y `- y₁)
  with x ≟ᵃʳ y
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᵃʳ y₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

module SETᵃʳ = SET {A = Arith} _≟ᵃʳ_

Set⟨Arith⟩ : Set
Set⟨Arith⟩ = Set' where open SETᵃʳ

_≟ᵖʳ_ : Decidable {A = Predicate} _≡_
`true ≟ᵖʳ `true = yes refl
`true ≟ᵖʳ (y `∧ y₁) = no (λ ())
`true ≟ᵖʳ (`¬ y) = no (λ ())
`true ≟ᵖʳ (x `= x₁) = no (λ ())
`true ≟ᵖʳ (x `< x₁) = no (λ ())

(x `∧ x₁) ≟ᵖʳ `true = no (λ ())
(x `∧ x₁) ≟ᵖʳ (y `∧ y₁)
  with x ≟ᵖʳ y
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᵖʳ y₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x `∧ x₁) ≟ᵖʳ (`¬ y) = no (λ ())
(x `∧ x₁) ≟ᵖʳ (x₂ `= x₃) = no (λ ())
(x `∧ x₁) ≟ᵖʳ (x₂ `< x₃) = no (λ ())

(`¬ x) ≟ᵖʳ `true = no (λ ())
(`¬ x) ≟ᵖʳ (y `∧ y₁) = no (λ ())
(`¬ x) ≟ᵖʳ (`¬ y)
  with x ≟ᵖʳ y
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(`¬ x) ≟ᵖʳ (x₁ `= x₂) = no (λ ())
(`¬ x) ≟ᵖʳ (x₁ `< x₂) = no (λ ())

(x `= x₁) ≟ᵖʳ `true = no (λ ())
(x `= x₁) ≟ᵖʳ (y `∧ y₁) = no (λ ())
(x `= x₁) ≟ᵖʳ (`¬ y) = no (λ ())
(x `= x₁) ≟ᵖʳ (x₂ `= x₃)
  with x ≟ᵃʳ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᵃʳ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x `= x₁) ≟ᵖʳ (x₂ `< x₃) = no (λ ())

(x `< x₁) ≟ᵖʳ `true = no (λ ())
(x `< x₁) ≟ᵖʳ (y `∧ y₁) = no (λ ())
(x `< x₁) ≟ᵖʳ (`¬ y) = no (λ ())
(x `< x₁) ≟ᵖʳ (x₂ `= x₃) = no (λ ())
(x `< x₁) ≟ᵖʳ (x₂ `< x₃)
  with x ≟ᵃʳ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᵃʳ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

module SETᵖʳ = SET {A = Predicate} _≟ᵖʳ_

Set⟨Predicate⟩ : Set
Set⟨Predicate⟩ = Set' where open SETᵖʳ
