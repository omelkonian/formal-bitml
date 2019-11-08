------------------------------------------------------------------------
-- Decidable equality for configurations.
------------------------------------------------------------------------

open import Data.Product using (Σ-syntax)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Maybe.Properties using (≡-dec)

open import Relation.Nullary using (yes; no)
open import Relation.Binary  using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Prelude.Set' as SET
open import Prelude.Lists

open import BitML.BasicTypes

module BitML.Semantics.Configurations.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types                     Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality         Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types             Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.DecidableEquality Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types      Participant _≟ₚ_ Honest

-------------------------------------------------------------------

-- Configurations.
_≟ᶜᶠ_ : Decidable {A = Configuration} _≡_
∅ᶜ ≟ᶜᶠ ∅ᶜ = yes refl
∅ᶜ ≟ᶜᶠ (` x) = no (λ ())
∅ᶜ ≟ᶜᶠ ⟨_,_⟩at_ x x₁ x₂ = no (λ ())
∅ᶜ ≟ᶜᶠ ⟨_has_⟩at_ x x₁ x₂ = no (λ ())
∅ᶜ ≟ᶜᶠ (x auth[ x₁ ]) = no (λ ())
∅ᶜ ≟ᶜᶠ ⟨ x ∶ x₁ ♯ x₂ ⟩ = no (λ ())
∅ᶜ ≟ᶜᶠ (x ∶ x₁ ♯ x₂) = no (λ ())
∅ᶜ ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

(` x) ≟ᶜᶠ ∅ᶜ = no (λ ())
(` x) ≟ᶜᶠ (` x₁)
  with x ≟ₐ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(` x) ≟ᶜᶠ ⟨_,_⟩at_ x₁ x₂ x₃ = no (λ ())
(` x) ≟ᶜᶠ ⟨_has_⟩at_ x₁ x₂ x₃ = no (λ ())
(` x) ≟ᶜᶠ (x₁ auth[ x₂ ]) = no (λ ())
(` x) ≟ᶜᶠ ⟨ x₁ ∶ x₂ ♯ x₃ ⟩ = no (λ ())
(` x) ≟ᶜᶠ (x₁ ∶ x₂ ♯ x₃) = no (λ ())
(` x) ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ ∅ᶜ = no (λ ())
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ (` x₃) = no (λ ())
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ ⟨_,_⟩at_ x₃ x₄ x₅
  with x ≟ᶜˢ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ℕ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ ⟨_has_⟩at_ x₃ x₄ x₅ = no (λ ())
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ (x₃ auth[ x₄ ]) = no (λ ())
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ ⟨ x₃ ∶ x₄ ♯ x₅ ⟩ = no (λ ())
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ (x₃ ∶ x₄ ♯ x₅) = no (λ ())
⟨_,_⟩at_ x x₁ x₂ ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ ∅ᶜ = no (λ ())
⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ (` x₂) = no (λ ())
⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ ⟨_,_⟩at_ x₂ x₃ x₄ = no (λ ())
⟨_has_⟩at_ x x₁ y ≟ᶜᶠ ⟨_has_⟩at_ x₂ x₃ y′
  with x ≟ₚ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ℕ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with y ≟ₛ y′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ (x₂ auth[ x₃ ]) = no (λ ())
⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ ⟨ x₂ ∶ x₃ ♯ x₄ ⟩ = no (λ ())
⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ (x₂ ∶ x₃ ♯ x₄) = no (λ ())
⟨_has_⟩at_ x x₁ _ ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

(x auth[ x₁ ]) ≟ᶜᶠ ∅ᶜ = no (λ ())
(x auth[ x₁ ]) ≟ᶜᶠ (` x₂) = no (λ ())
(x auth[ x₁ ]) ≟ᶜᶠ ⟨_,_⟩at_ x₂ x₃ x₄ = no (λ ())
(x auth[ x₁ ]) ≟ᶜᶠ ⟨_has_⟩at_ x₂ x₃ _ = no (λ ())
(x auth[ x₁ ]) ≟ᶜᶠ (x₂ auth[ x₃ ])
  with x ≟ₚ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᵃᶜ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x auth[ x₁ ]) ≟ᶜᶠ ⟨ x₂ ∶ x₃ ♯ x₄ ⟩ = no (λ ())
(x auth[ x₁ ]) ≟ᶜᶠ (x₂ ∶ x₃ ♯ x₄) = no (λ ())
(x auth[ x₁ ]) ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ ∅ᶜ = no (λ ())
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ (` x₃) = no (λ ())
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ ⟨_,_⟩at_ x₃ x₄ x₅ = no (λ ())
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ ⟨_has_⟩at_ x₃ x₄ _ = no (λ ())
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ (x₃ auth[ x₄ ]) = no (λ ())
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ ⟨ x₃ ∶ x₄ ♯ x₅ ⟩
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with ≡-dec _≟ℕ_ x₂ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ (x₃ ∶ x₄ ♯ x₅) = no (λ ())
⟨ x ∶ x₁ ♯ x₂ ⟩ ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

(x ∶ x₁ ♯ x₂) ≟ᶜᶠ ∅ᶜ = no (λ ())
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ (` x₃) = no (λ ())
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ ⟨_,_⟩at_ x₃ x₄ x₅ = no (λ ())
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ ⟨_has_⟩at_ x₃ x₄ _ = no (λ ())
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ (x₃ auth[ x₄ ]) = no (λ ())
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ ⟨ x₃ ∶ x₄ ♯ x₅ ⟩ = no (λ ())
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ (x₃ ∶ x₄ ♯ x₅)
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ℕ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x ∶ x₁ ♯ x₂) ≟ᶜᶠ (c′ ∣ c′₁) = no (λ ())

(c ∣ c₁) ≟ᶜᶠ ∅ᶜ = no (λ ())
(c ∣ c₁) ≟ᶜᶠ (` x) = no (λ ())
(c ∣ c₁) ≟ᶜᶠ ⟨_,_⟩at_ x x₁ x₂ = no (λ ())
(c ∣ c₁) ≟ᶜᶠ ⟨_has_⟩at_ x x₁ _ = no (λ ())
(c ∣ c₁) ≟ᶜᶠ (x auth[ x₁ ]) = no (λ ())
(c ∣ c₁) ≟ᶜᶠ ⟨ x ∶ x₁ ♯ x₂ ⟩ = no (λ ())
(c ∣ c₁) ≟ᶜᶠ (x ∶ x₁ ♯ x₂) = no (λ ())
(c ∣ c₁) ≟ᶜᶠ (c′ ∣ c′₁)
  with c ≟ᶜᶠ c′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with c₁ ≟ᶜᶠ c′₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

module SETᶜᶠ = SET _≟ᶜᶠ_
Set⟨Configuration⟩ = Set' where open SETᶜᶠ
