------------------------------------------------------------------------
-- Decidable equality for predicates.
------------------------------------------------------------------------
module BitML.Predicate.DecidableEquality where

open import Data.Product using (_,_)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)
open import Data.Fin     using (Fin)
  renaming (_≟_ to _≟ᶠ_)
open import Data.Integer using (ℤ)
  renaming (_≟_ to _≟ℤ_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import BitML.Predicate.Base

import Prelude.Set' as SET

_≟ᶜᵗˣ_ : Decidable {A = ExpressionContext} _≡_
(Ctx n) ≟ᶜᵗˣ (Ctx n′)
  with n ≟ℕ n′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_≟∃ᵉˣ_ : Decidable {A = ∃Expression} _≡_
(ctx , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`ℤ , ∣ x₁ ∣)
  with ctx ≟ᶜᵗˣ ctx′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ᶠ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₁)) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(.(Ctx _) , .`ℤ , ∣ x ∣) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₁ ∣) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₁))
  with ctx ≟ᶜᵗˣ ctx′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ℤ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`ℤ , (` x)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₂ ∣) = no (λ ())
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₂)) = no (λ ())
(ctx , .`ℤ , (x `+ y)) ≟∃ᵉˣ (ctx′ , .`ℤ , (x′ `+ y′))
  with (ctx , `ℤ , x) ≟∃ᵉˣ (ctx′ , `ℤ , x′) | (ctx , `ℤ , y) ≟∃ᵉˣ (ctx′ , `ℤ , y′)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`ℤ , (x `+ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₂ ∣) = no (λ ())
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₂)) = no (λ ())
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`ℤ , (x `- y)) ≟∃ᵉˣ (ctx′ , .`ℤ , (x′ `- y′))
  with (ctx , `ℤ , x) ≟∃ᵉˣ (ctx′ , `ℤ , x′) | (ctx , `ℤ , y) ≟∃ᵉˣ (ctx′ , `ℤ , y′)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`ℤ , (x `- x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₂ ∣) = no (λ ())
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₂)) = no (λ ())
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`Bool , (x `= y)) ≟∃ᵉˣ (ctx′ , .`Bool , (x′ `= y′))
  with (ctx , `ℤ , x) ≟∃ᵉˣ (ctx′ , `ℤ , x′) | (ctx , `ℤ , y) ≟∃ᵉˣ (ctx′ , `ℤ , y′)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`Bool , (x `= x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₂ ∣) = no (λ ())
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₂)) = no (λ ())
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`Bool , (x `< y)) ≟∃ᵉˣ (ctx′ , .`Bool , (x′ `< y′))
  with (ctx , `ℤ , x) ≟∃ᵉˣ (ctx′ , `ℤ , x′) | (ctx , `ℤ , y) ≟∃ᵉˣ (ctx′ , `ℤ , y′)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`Bool , (x `< x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`Bool , `true) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x ∣) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x)) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`Bool , `true)
  with ctx ≟ᶜᵗˣ ctx′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`Bool , `true) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₂ ∣) = no (λ ())
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₂)) = no (λ ())
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`Bool , (x `∧ y)) ≟∃ᵉˣ (ctx′ , .`Bool , (x′ `∧ y′))
  with (ctx , `Bool , x) ≟∃ᵉˣ (ctx′ , `Bool , x′) | (ctx , `Bool , y) ≟∃ᵉˣ (ctx′ , `Bool , y′)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(ctx , .`Bool , (x `∧ x₁)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y)) = no (λ ())

(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (.(Ctx _) , .`ℤ , ∣ x₁ ∣) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`ℤ , (` x₁)) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `+ y₁)) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`ℤ , (y `- y₁)) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `= y₁)) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `< y₁)) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`Bool , `true) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`Bool , (y `∧ y₁)) = no (λ ())
(ctx , .`Bool , (`¬ x)) ≟∃ᵉˣ (ctx′ , .`Bool , (`¬ y))
  with (ctx , `Bool , x) ≟∃ᵉˣ (ctx′ , `Bool , y)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_≟ᵉˣ_ : Decidable {A = Expression ctx ty} _≡_
_≟ᵉˣ_ {ctx = ctx} {ty = ty} x y
  with (ctx , ty , x) ≟∃ᵉˣ (ctx , ty , y)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

module SETᵉˣ = SET {A = ∃Expression} _≟∃ᵉˣ_

Set⟨Expression⟩ : Set
Set⟨Expression⟩ = Set' where open SETᵉˣ

_≟∃ᵖʳ_ : Decidable {A = ∃Predicate} _≡_
(ctx , x) ≟∃ᵖʳ (ctx′ , y)
  with ctx ≟ᶜᵗˣ ctx′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ᵉˣ y
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_≟ᵖʳ_ : Decidable {A = Predicate ctx} _≡_
_≟ᵖʳ_ {ctx = ctx} x y
  with (ctx , x) ≟∃ᵖʳ (ctx , y)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

module SETᵖʳ = SET {A = ∃Predicate} _≟∃ᵖʳ_

Set⟨Predicate⟩ : Set
Set⟨Predicate⟩ = Set' where open SETᵖʳ
