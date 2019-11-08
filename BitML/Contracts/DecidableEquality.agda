------------------------------------------------------------------------
-- Decidable equality for contracts and advertisements
------------------------------------------------------------------------
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Bool    using ()
  renaming (_≟_ to _≟ᵇ_)
open import Data.Nat     using (_>_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; length; []; _∷_)

open import Relation.Nullary using (yes; no)
open import Relation.Binary  using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import BitML.BasicTypes
open import BitML.Predicate.DecidableEquality

module BitML.Contracts.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types   Participant _≟ₚ_ Honest

import Prelude.Set' as SET

-- Deposits.
_≟ₑ_ : Decidable {A = DepositRef} _≡_
(p , v , x) ≟ₑ (p′ , v′ , x′)
  with p ≟ₚ p′ | v ≟ℕ v′ | x ≟ₛ x′
... | no ¬p    | _        | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl | yes refl = yes refl

module SETₑ = SET _≟ₑ_
Set⟨DepositRef⟩ : Set
Set⟨DepositRef⟩ = Set' where open SETₑ

-- Contracts.
_≟ᶜ_ : Decidable {A = Contract} _≡_
_≟ᶜˢ_ : Decidable {A = Contracts} _≡_
_≟ᵛᶜˢ_ : Decidable {A = List (Value × Contracts)} _≡_

(put x &reveal x₁ if x₂ ⇒ x₃) ≟ᶜ (put x₄ &reveal x₅ if x₆ ⇒ x₇)
  with x SETₛ.≟ₗ x₄
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₁ SETₛ.≟ₗ x₅
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₂ ≟ᵖʳ x₆
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₃ ≟ᶜˢ x₇
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(put x &reveal x₁ if x₂ ⇒ x₃) ≟ᶜ withdraw x₄ = no (λ ())
(put x &reveal x₁ if x₂ ⇒ x₃) ≟ᶜ split x₄ = no (λ ())
(put x &reveal x₁ if x₂ ⇒ x₃) ≟ᶜ (x₄ ⇒ c′) = no (λ ())
(put x &reveal x₁ if x₂ ⇒ x₃) ≟ᶜ (after x₄ ⇒ c′) = no (λ ())

withdraw x ≟ᶜ (put x₁ &reveal x₂ if x₃ ⇒ x₄) = no (λ ())
withdraw x ≟ᶜ withdraw x₁
  with x ≟ₚ x₁
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
withdraw x ≟ᶜ split x₁ = no (λ ())
withdraw x ≟ᶜ (x₁ ⇒ c′) = no (λ ())
withdraw x ≟ᶜ (after x₁ ⇒ c′) = no (λ ())

split x ≟ᶜ (put x₁ &reveal x₂ if x₃ ⇒ x₄) = no (λ ())
split x ≟ᶜ withdraw x₁ = no (λ ())
split x ≟ᶜ split x₁
  with x ≟ᵛᶜˢ x₁
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
split x ≟ᶜ (x₁ ⇒ c′) = no (λ ())
split x ≟ᶜ (after x₁ ⇒ c′) = no (λ ())

(x ⇒ c) ≟ᶜ (put x₁ &reveal x₂ if x₃ ⇒ x₄) = no (λ ())
(x ⇒ c) ≟ᶜ withdraw x₁ = no (λ ())
(x ⇒ c) ≟ᶜ split x₁ = no (λ ())
(x ⇒ c) ≟ᶜ (x₁ ⇒ c′)
  with x ≟ₚ x₁
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(x ⇒ c) ≟ᶜ (after x₁ ⇒ c′) = no (λ ())

(after x ⇒ c) ≟ᶜ (put x₁ &reveal x₂ if x₃ ⇒ x₄) = no (λ ())
(after x ⇒ c) ≟ᶜ withdraw x₁ = no (λ ())
(after x ⇒ c) ≟ᶜ split x₁ = no (λ ())
(after x ⇒ c) ≟ᶜ (x₁ ⇒ c′) = no (λ ())
(after x ⇒ c) ≟ᶜ (after x₁ ⇒ c′)
  with x ≟ℕ x₁
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

[] ≟ᶜˢ [] = yes refl
[] ≟ᶜˢ (x ∷ cs′) = no (λ ())
(x ∷ cs) ≟ᶜˢ [] = no (λ ())
(x ∷ cs) ≟ᶜˢ (x₁ ∷ cs′)
  with x ≟ᶜ x₁
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with cs ≟ᶜˢ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

[] ≟ᵛᶜˢ [] = yes refl
[] ≟ᵛᶜˢ (x ∷ cs′) = no (λ ())
(x ∷ cs) ≟ᵛᶜˢ [] = no (λ ())
((v , cs) ∷ vcs) ≟ᵛᶜˢ ((v′ , cs′) ∷ vcs′)
  with v ≟ℕ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with cs ≟ᶜˢ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with vcs ≟ᵛᶜˢ vcs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETᶜ = SET _≟ᶜ_
Set⟨Contract⟩ : Set
Set⟨Contract⟩ = Set' where open SETᶜ

module SETᶜˢ = SET _≟ᶜˢ_
Set⟨Contracts⟩ : Set
Set⟨Contracts⟩ = Set' where open SETᶜˢ

-- Sets of preconditions.
_≟ᵖ_ : Decidable {A = Precondition} _≡_
(x :? x₁ at x₂) ≟ᵖ (x₃ :? x₄ at x₅)
  with x ≟ₚ x₃
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₁ ≟ℕ x₄
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(x :? x₁ at x₂) ≟ᵖ (x₃ :! x₄ at x₅) = no (λ ())
(x :? x₁ at x₂) ≟ᵖ (x₃ :secret x₄) = no (λ ())
(x :? x₁ at x₂) ≟ᵖ (p′ ∣∣ p′₁) = no (λ ())

(x :! x₁ at x₂) ≟ᵖ (x₃ :? x₄ at x₅) = no (λ ())
(x :! x₁ at x₂) ≟ᵖ (x₃ :! x₄ at x₅)
  with x ≟ₚ x₃
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₁ ≟ℕ x₄
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(x :! x₁ at x₂) ≟ᵖ (x₃ :secret x₄) = no (λ ())
(x :! x₁ at x₂) ≟ᵖ (p′ ∣∣ p′₁) = no (λ ())

(x :secret x₁) ≟ᵖ (x₂ :? x₃ at x₄) = no (λ ())
(x :secret x₁) ≟ᵖ (x₂ :! x₃ at x₄) = no (λ ())
(x :secret x₁) ≟ᵖ (x₂ :secret x₃)
  with x ≟ₚ x₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x₁ ≟ₛ x₃
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(x :secret x₁) ≟ᵖ (p′ ∣∣ p′₁) = no (λ ())

(p ∣∣ p₁) ≟ᵖ (x :? x₁ at x₂) = no (λ ())
(p ∣∣ p₁) ≟ᵖ (x :! x₁ at x₂) = no (λ ())
(p ∣∣ p₁) ≟ᵖ (x :secret x₁) = no (λ ())
(p ∣∣ p₁) ≟ᵖ (p′ ∣∣ p′₁)
  with p ≟ᵖ p′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with p₁ ≟ᵖ p′₁
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

-- Advertisements.
_≟ₐ_ : Decidable {A = Advertisement} _≡_
(⟨ G ⟩ C) ≟ₐ (⟨ G′ ⟩ C′)
  with G ≟ᵖ G′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with C ≟ᶜˢ C′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₐ = SET _≟ₐ_
Set⟨Advertisement⟩ : Set
Set⟨Advertisement⟩ = Set' where open SETₐ
