------------------------------------------------------------------------
-- Decidable equality for actions
------------------------------------------------------------------------

open import Data.Nat     using (ℕ; _>_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ-syntax)
open import Data.List    using (List; length)
open import Data.Fin     using ()
  renaming (_≟_ to _≟ᶠ_)

open import Relation.Nullary           using (yes; no)
open import Relation.Binary            using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Prelude.Set' as SET
open import Prelude.Lists

open import BitML.BasicTypes

module BitML.Semantics.Actions.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types             Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types     Participant _≟ₚ_ Honest

------------------------------------------------------------------------

-- Actions.
_≟ᵃᶜ_ : Decidable {A = Action} _≡_
(♯▷ x) ≟ᵃᶜ (♯▷ x₁)
  with x ≟ₐ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(♯▷ x) ≟ᵃᶜ (x₁ ▷ˢ x₂) = no (λ ())
(♯▷ x) ≟ᵃᶜ (x₁ ▷ x₂) = no (λ ())
(♯▷ x) ≟ᵃᶜ (x₁ ↔ x₂ ▷⟨ x₃ , _ ⟩) = no (λ ())
(♯▷ x) ≟ᵃᶜ (x₁ ▷⟨ A , v , v₂ ⟩) = no (λ ())
(♯▷ x) ≟ᵃᶜ (x₁ ▷ᵈ x₂) = no (λ ())
(♯▷ x) ≟ᵃᶜ (xs , i ▷ᵈˢ x₁) = no (λ ())

(x ▷ˢ x₁) ≟ᵃᶜ (♯▷ x₂) = no (λ ())
(x ▷ˢ x₁) ≟ᵃᶜ (x₂ ▷ˢ x₃)
  with x ≟ₛ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₐ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x ▷ˢ x₁) ≟ᵃᶜ (x₂ ▷ x₃) = no (λ ())
(x ▷ˢ x₁) ≟ᵃᶜ (x₂ ↔ x₃ ▷⟨ x₄ , _ ⟩) = no (λ ())
(x ▷ˢ x₁) ≟ᵃᶜ (x₂ ▷⟨ A , v , v₂ ⟩) = no (λ ())
(x ▷ˢ x₁) ≟ᵃᶜ (x₂ ▷ᵈ x₃) = no (λ ())
(x ▷ˢ x₁) ≟ᵃᶜ (xs , i ▷ᵈˢ x₂) = no (λ ())

(x ▷ x₁) ≟ᵃᶜ (♯▷ x₂) = no (λ ())
(x ▷ x₁) ≟ᵃᶜ (x₂ ▷ˢ x₃) = no (λ ())
(x ▷ x₁) ≟ᵃᶜ (x₂ ▷ x₃)
  with x ≟ₛ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᶜ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x ▷ x₁) ≟ᵃᶜ (x₂ ↔ x₃ ▷⟨ x₄ , _ ⟩) = no (λ ())
(x ▷ x₁) ≟ᵃᶜ (x₂ ▷⟨ A , v , v₂ ⟩) = no (λ ())
(x ▷ x₁) ≟ᵃᶜ (x₂ ▷ᵈ x₃) = no (λ ())
(x ▷ x₁) ≟ᵃᶜ (xs , i ▷ᵈˢ x₂) = no (λ ())

(x ↔ x₁ ▷⟨ x₂ , _ ⟩) ≟ᵃᶜ (♯▷ x₃) = no (λ ())
(x ↔ x₁ ▷⟨ x₂ , _ ⟩) ≟ᵃᶜ (x₃ ▷ˢ x₄) = no (λ ())
(x ↔ x₁ ▷⟨ x₂ , _ ⟩) ≟ᵃᶜ (x₃ ▷ x₄) = no (λ ())
(x ↔ x₁ ▷⟨ x₂ , v ⟩) ≟ᵃᶜ (x₃ ↔ x₄ ▷⟨ x₅ , v′ ⟩)
  with x ≟ₛ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₚ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with v ≟ℕ v′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x ↔ x₁ ▷⟨ x₂ , _ ⟩) ≟ᵃᶜ (x₃ ▷⟨ A , v , v₂ ⟩) = no (λ ())
(x ↔ x₁ ▷⟨ x₂ , _ ⟩) ≟ᵃᶜ (x₃ ▷ᵈ x₄) = no (λ ())
(x ↔ x₁ ▷⟨ x₂ , _ ⟩) ≟ᵃᶜ (xs , i ▷ᵈˢ x₃) = no (λ ())

(x ▷⟨ A , v , v₂ ⟩) ≟ᵃᶜ (♯▷ x₃) = no (λ ())
(x ▷⟨ A , v , v₂ ⟩) ≟ᵃᶜ (x₃ ▷ˢ x₄) = no (λ ())
(x ▷⟨ A , v , v₂ ⟩) ≟ᵃᶜ (x₃ ▷ x₄) = no (λ ())
(x ▷⟨ A , v , v₂ ⟩) ≟ᵃᶜ (x₃ ↔ x₄ ▷⟨ x₅ , _ ⟩) = no (λ ())
(x ▷⟨ A , v , v′ ⟩) ≟ᵃᶜ (x₃ ▷⟨ A′ , w , w′ ⟩)
  with x ≟ₛ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with A ≟ₚ A′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with v ≟ℕ w
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with v′ ≟ℕ w′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x ▷⟨ A , v , v₂ ⟩) ≟ᵃᶜ (x₃ ▷ᵈ x₄) = no (λ ())
(x ▷⟨ A , v , v₂ ⟩) ≟ᵃᶜ (xs , i ▷ᵈˢ x₃) = no (λ ())

(x ▷ᵈ x₁) ≟ᵃᶜ (♯▷ x₂) = no (λ ())
(x ▷ᵈ x₁) ≟ᵃᶜ (x₂ ▷ˢ x₃) = no (λ ())
(x ▷ᵈ x₁) ≟ᵃᶜ (x₂ ▷ x₃) = no (λ ())
(x ▷ᵈ x₁) ≟ᵃᶜ (x₂ ↔ x₃ ▷⟨ x₄ , _ ⟩) = no (λ ())
(x ▷ᵈ x₁) ≟ᵃᶜ (x₂ ▷⟨ A , v , v₂ ⟩) = no (λ ())
(x ▷ᵈ A) ≟ᵃᶜ (x₂ ▷ᵈ A′)
  with x ≟ₛ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with A ≟ₚ A′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(x ▷ᵈ x₁) ≟ᵃᶜ (xs , i ▷ᵈˢ x₂) = no (λ ())

(xs , i ▷ᵈˢ x) ≟ᵃᶜ (♯▷ x₁) = no (λ ())
(xs , i ▷ᵈˢ x) ≟ᵃᶜ (x₁ ▷ˢ x₂) = no (λ ())
(xs , i ▷ᵈˢ x) ≟ᵃᶜ (x₁ ▷ x₂) = no (λ ())
(xs , i ▷ᵈˢ x) ≟ᵃᶜ (x₁ ↔ x₂ ▷⟨ x₃ , _ ⟩) = no (λ ())
(xs , i ▷ᵈˢ x) ≟ᵃᶜ (x₁ ▷⟨ A , v , v₂ ⟩) = no (λ ())
(xs , i ▷ᵈˢ x) ≟ᵃᶜ (x₁ ▷ᵈ x₂) = no (λ ())
(xs , i ▷ᵈˢ x) ≟ᵃᶜ (xs₁ , i₁ ▷ᵈˢ x₁)
  with xs SETₛ.≟ₗ xs₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with i ≟ᶠ i₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ₛ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

module SETᵃᶜ = SET _≟ᵃᶜ_
Set⟨Action⟩ : Set
Set⟨Action⟩ = Set' where open SETᵃᶜ
