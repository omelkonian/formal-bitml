------------------------------------------------------------------------
-- Decidable equality for labels.
------------------------------------------------------------------------

open import Data.Nat     using (ℕ; _>_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Fin     using ()
  renaming (_≟_ to _≟ᶠ_)
open import Data.List    using (List; length; []; _∷_)
open import Data.Maybe   using (Maybe)
open import Data.Maybe.Properties using (≡-dec)

open import Relation.Nullary using (yes; no)
open import Relation.Binary  using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import BitML.BasicTypes

module BitML.Semantics.Labels.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types             Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types      Participant _≟ₚ_ Honest

------------------------------------------------------------------------

_≟ₗ′_ : Decidable {A = List (Secret × Maybe ℕ)} _≡_
[] ≟ₗ′ [] = yes refl
[] ≟ₗ′ (_ ∷ _) = no λ ()
(_ ∷ _) ≟ₗ′ [] = no λ ()
((s , m) ∷ xs) ≟ₗ′ ((s′ , m′) ∷ xs′)
  with s ≟ₛ s′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with ≡-dec _≟ℕ_ m m′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with xs ≟ₗ′ xs′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

-- Actions.
_≟ˡ_ : Decidable {A = Label} _≡_
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ]
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ] = no (λ ())
auth-join[ x , x₁ ↔ x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

join[ x ↔ x₁ ] ≟ˡ auth-join[ x₂ , x₃ ↔ x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ join[ x₂ ↔ x₃ ]
  with x ≟ₛ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
join[ x ↔ x₁ ] ≟ˡ auth-divide[ x₂ , x₃ ▷ x₄ , x₅ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ divide[ x₂ ▷ x₃ , x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ auth-donate[ x₂ , x₃ ▷ᵈ x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ donate[ x₂ ▷ᵈ x₃ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ auth-destroy[ x₂ , xs , x₃ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ destroy[ x₂ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ advertise[ x₂ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ auth-commit[ x₂ , x₃ , x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ auth-init[ x₂ , x₃ , x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ init[ x₂ , x₃ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ split[ x₂ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ auth-rev[ x₂ , x₃ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ put[ x₂ , x₃ , x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ withdraw[ x₂ , x₃ , x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ auth-control[ x₂ , x₃ ▷ x₄ ] = no (λ ())
join[ x ↔ x₁ ] ≟ˡ delay[ x₂ ] = no (λ ())

auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-join[ x₄ , x₅ ↔ x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ join[ x₄ ↔ x₅ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-divide[ x₄ , x₅ ▷ x₆ , x₇ ]
  with x ≟ₚ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ℕ x₆
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₃ ≟ℕ x₇
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ divide[ x₄ ▷ x₅ , x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-donate[ x₄ , x₅ ▷ᵈ x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ donate[ x₄ ▷ᵈ x₅ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-destroy[ x₄ , xs , x₅ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ destroy[ x₄ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ advertise[ x₄ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-commit[ x₄ , x₅ , x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-init[ x₄ , x₅ , x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ init[ x₄ , x₅ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ split[ x₄ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-rev[ x₄ , x₅ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ put[ x₄ , x₅ , x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ withdraw[ x₄ , x₅ , x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ auth-control[ x₄ , x₅ ▷ x₆ ] = no (λ ())
auth-divide[ x , x₁ ▷ x₂ , x₃ ] ≟ˡ delay[ x₄ ] = no (λ ())

divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ]
  with x ≟ₛ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ℕ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ℕ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ] = no (λ ())
divide[ x ▷ x₁ , x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ]
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₚ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ] = no (λ ())
auth-donate[ x , x₁ ▷ᵈ x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

donate[ x ▷ᵈ x₁ ] ≟ˡ auth-join[ x₂ , x₃ ↔ x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ join[ x₂ ↔ x₃ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-divide[ x₂ , x₃ ▷ x₄ , x₅ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ divide[ x₂ ▷ x₃ , x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-donate[ x₂ , x₃ ▷ᵈ x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ donate[ x₂ ▷ᵈ x₃ ]
  with x ≟ₛ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-destroy[ x₂ , xs , x₃ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ destroy[ x₂ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ advertise[ x₂ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-commit[ x₂ , x₃ , x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-init[ x₂ , x₃ , x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ init[ x₂ , x₃ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ split[ x₂ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-rev[ x₂ , x₃ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ put[ x₂ , x₃ , x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ withdraw[ x₂ , x₃ , x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ auth-control[ x₂ , x₃ ▷ x₄ ] = no (λ ())
donate[ x ▷ᵈ x₁ ] ≟ˡ delay[ x₂ ] = no (λ ())

auth-destroy[ x , xs , x₁ ] ≟ˡ auth-join[ x₂ , x₃ ↔ x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ join[ x₂ ↔ x₃ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-divide[ x₂ , x₃ ▷ x₄ , x₅ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ divide[ x₂ ▷ x₃ , x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-donate[ x₂ , x₃ ▷ᵈ x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ donate[ x₂ ▷ᵈ x₃ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-destroy[ x₂ , xs₁ , x₃ ]
  with x ≟ₚ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with xs SETₛ.≟ₗ xs₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᶠ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-destroy[ x , xs , x₁ ] ≟ˡ destroy[ x₂ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ advertise[ x₂ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-commit[ x₂ , x₃ , x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-init[ x₂ , x₃ , x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ init[ x₂ , x₃ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ split[ x₂ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-rev[ x₂ , x₃ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ put[ x₂ , x₃ , x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ withdraw[ x₂ , x₃ , x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ auth-control[ x₂ , x₃ ▷ x₄ ] = no (λ ())
auth-destroy[ x , xs , x₁ ] ≟ˡ delay[ x₂ ] = no (λ ())

destroy[ x ] ≟ˡ auth-join[ x₁ , x₂ ↔ x₃ ] = no (λ ())
destroy[ x ] ≟ˡ join[ x₁ ↔ x₂ ] = no (λ ())
destroy[ x ] ≟ˡ auth-divide[ x₁ , x₂ ▷ x₃ , x₄ ] = no (λ ())
destroy[ x ] ≟ˡ divide[ x₁ ▷ x₂ , x₃ ] = no (λ ())
destroy[ x ] ≟ˡ auth-donate[ x₁ , x₂ ▷ᵈ x₃ ] = no (λ ())
destroy[ x ] ≟ˡ donate[ x₁ ▷ᵈ x₂ ] = no (λ ())
destroy[ x ] ≟ˡ auth-destroy[ x₁ , xs , x₂ ] = no (λ ())
destroy[ x ] ≟ˡ destroy[ x₁ ]
  with x SETₛ.≟ₗ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
destroy[ x ] ≟ˡ advertise[ x₁ ] = no (λ ())
destroy[ x ] ≟ˡ auth-commit[ x₁ , x₂ , x₃ ] = no (λ ())
destroy[ x ] ≟ˡ auth-init[ x₁ , x₂ , x₃ ] = no (λ ())
destroy[ x ] ≟ˡ init[ x₁ , x₂ ] = no (λ ())
destroy[ x ] ≟ˡ split[ x₁ ] = no (λ ())
destroy[ x ] ≟ˡ auth-rev[ x₁ , x₂ ] = no (λ ())
destroy[ x ] ≟ˡ put[ x₁ , x₂ , x₃ ] = no (λ ())
destroy[ x ] ≟ˡ withdraw[ x₁ , x₂ , x₃ ] = no (λ ())
destroy[ x ] ≟ˡ auth-control[ x₁ , x₂ ▷ x₃ ] = no (λ ())
destroy[ x ] ≟ˡ delay[ x₁ ] = no (λ ())

advertise[ x ] ≟ˡ auth-join[ x₁ , x₂ ↔ x₃ ] = no (λ ())
advertise[ x ] ≟ˡ join[ x₁ ↔ x₂ ] = no (λ ())
advertise[ x ] ≟ˡ auth-divide[ x₁ , x₂ ▷ x₃ , x₄ ] = no (λ ())
advertise[ x ] ≟ˡ divide[ x₁ ▷ x₂ , x₃ ] = no (λ ())
advertise[ x ] ≟ˡ auth-donate[ x₁ , x₂ ▷ᵈ x₃ ] = no (λ ())
advertise[ x ] ≟ˡ donate[ x₁ ▷ᵈ x₂ ] = no (λ ())
advertise[ x ] ≟ˡ auth-destroy[ x₁ , xs , x₂ ] = no (λ ())
advertise[ x ] ≟ˡ destroy[ x₁ ] = no (λ ())
advertise[ x ] ≟ˡ advertise[ x₁ ]
  with x ≟ₐ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
advertise[ x ] ≟ˡ auth-commit[ x₁ , x₂ , x₃ ] = no (λ ())
advertise[ x ] ≟ˡ auth-init[ x₁ , x₂ , x₃ ] = no (λ ())
advertise[ x ] ≟ˡ init[ x₁ , x₂ ] = no (λ ())
advertise[ x ] ≟ˡ split[ x₁ ] = no (λ ())
advertise[ x ] ≟ˡ auth-rev[ x₁ , x₂ ] = no (λ ())
advertise[ x ] ≟ˡ put[ x₁ , x₂ , x₃ ] = no (λ ())
advertise[ x ] ≟ˡ withdraw[ x₁ , x₂ , x₃ ] = no (λ ())
advertise[ x ] ≟ˡ auth-control[ x₁ , x₂ ▷ x₃ ] = no (λ ())
advertise[ x ] ≟ˡ delay[ x₁ ] = no (λ ())

auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ]
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₐ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₗ′ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ] = no (λ ())
auth-commit[ x , x₁ , x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

auth-init[ x , x₁ , x₂ ] ≟ˡ auth-join[ _ , _ ↔ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ join[ _ ↔ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-divide[ _ , _ ▷ _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ divide[ _ ▷ _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-donate[ _ , _ ▷ᵈ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ donate[ _ ▷ᵈ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-destroy[ _ , _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ destroy[ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ advertise[ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-commit[ _ , _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ]
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₐ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-init[ x , x₁ , x₂ ] ≟ˡ init[ _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ split[ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-rev[ _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ put[ _ , _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ withdraw[ _ , _ , _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ auth-control[ _ , _ ▷ _ ] = no (λ ())
auth-init[ x , x₁ , x₂ ] ≟ˡ delay[ _ ] = no (λ ())

init[ x , x₁ ] ≟ˡ auth-join[ x₂ , x₃ ↔ x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ join[ x₂ ↔ x₃ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-divide[ x₂ , x₃ ▷ x₄ , x₅ ] = no (λ ())
init[ x , x₁ ] ≟ˡ divide[ x₂ ▷ x₃ , x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-donate[ x₂ , x₃ ▷ᵈ x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ donate[ x₂ ▷ᵈ x₃ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-destroy[ x₂ , xs , x₃ ] = no (λ ())
init[ x , x₁ ] ≟ˡ destroy[ x₂ ] = no (λ ())
init[ x , x₁ ] ≟ˡ advertise[ x₂ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-commit[ x₂ , x₃ , x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-init[ x₂ , x₃ , x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ init[ x₂ , x₃ ]
  with x ≟ᵖ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ᶜˢ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
init[ x , x₁ ] ≟ˡ split[ x₂ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-rev[ x₂ , x₃ ] = no (λ ())
init[ x , x₁ ] ≟ˡ put[ x₂ , x₃ , x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ withdraw[ x₂ , x₃ , x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ auth-control[ x₂ , x₃ ▷ x₄ ] = no (λ ())
init[ x , x₁ ] ≟ˡ delay[ x₂ ] = no (λ ())

split[ x ] ≟ˡ auth-join[ x₁ , x₂ ↔ x₃ ] = no (λ ())
split[ x ] ≟ˡ join[ x₁ ↔ x₂ ] = no (λ ())
split[ x ] ≟ˡ auth-divide[ x₁ , x₂ ▷ x₃ , x₄ ] = no (λ ())
split[ x ] ≟ˡ divide[ x₁ ▷ x₂ , x₃ ] = no (λ ())
split[ x ] ≟ˡ auth-donate[ x₁ , x₂ ▷ᵈ x₃ ] = no (λ ())
split[ x ] ≟ˡ donate[ x₁ ▷ᵈ x₂ ] = no (λ ())
split[ x ] ≟ˡ auth-destroy[ x₁ , xs , x₂ ] = no (λ ())
split[ x ] ≟ˡ destroy[ x₁ ] = no (λ ())
split[ x ] ≟ˡ advertise[ x₁ ] = no (λ ())
split[ x ] ≟ˡ auth-commit[ x₁ , x₂ , x₃ ] = no (λ ())
split[ x ] ≟ˡ auth-init[ x₁ , x₂ , x₃ ] = no (λ ())
split[ x ] ≟ˡ init[ x₁ , x₂ ] = no (λ ())
split[ x ] ≟ˡ split[ x₁ ]
  with x ≟ₛ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
split[ x ] ≟ˡ auth-rev[ x₁ , x₂ ] = no (λ ())
split[ x ] ≟ˡ put[ x₁ , x₂ , x₃ ] = no (λ ())
split[ x ] ≟ˡ withdraw[ x₁ , x₂ , x₃ ] = no (λ ())
split[ x ] ≟ˡ auth-control[ x₁ , x₂ ▷ x₃ ] = no (λ ())
split[ x ] ≟ˡ delay[ x₁ ] = no (λ ())

auth-rev[ x , x₁ ] ≟ˡ auth-join[ x₂ , x₃ ↔ x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ join[ x₂ ↔ x₃ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-divide[ x₂ , x₃ ▷ x₄ , x₅ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ divide[ x₂ ▷ x₃ , x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-donate[ x₂ , x₃ ▷ᵈ x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ donate[ x₂ ▷ᵈ x₃ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-destroy[ x₂ , xs , x₃ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ destroy[ x₂ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ advertise[ x₂ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-commit[ x₂ , x₃ , x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-init[ x₂ , x₃ , x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ init[ x₂ , x₃ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ split[ x₂ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-rev[ x₂ , x₃ ]
  with x ≟ₚ x₂
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-rev[ x , x₁ ] ≟ˡ put[ x₂ , x₃ , x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ withdraw[ x₂ , x₃ , x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ auth-control[ x₂ , x₃ ▷ x₄ ] = no (λ ())
auth-rev[ x , x₁ ] ≟ˡ delay[ x₂ ] = no (λ ())

put[ x , x₁ , x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ]
  with x SETₛ.≟ₗ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ SETₛ.≟ₗ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
put[ x , x₁ , x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ] = no (λ ())
put[ x , x₁ , x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

withdraw[ x , x₁ , x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ]
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ℕ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ₛ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
withdraw[ x , x₁ , x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ] = no (λ ())
withdraw[ x , x₁ , x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-join[ x₃ , x₄ ↔ x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ join[ x₃ ↔ x₄ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-divide[ x₃ , x₄ ▷ x₅ , x₆ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ divide[ x₃ ▷ x₄ , x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-donate[ x₃ , x₄ ▷ᵈ x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ donate[ x₃ ▷ᵈ x₄ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-destroy[ x₃ , xs , x₄ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ destroy[ x₃ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ advertise[ x₃ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-commit[ x₃ , x₄ , x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-init[ x₃ , x₄ , x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ init[ x₃ , x₄ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ split[ x₃ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-rev[ x₃ , x₄ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ put[ x₃ , x₄ , x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ withdraw[ x₃ , x₄ , x₅ ] = no (λ ())
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ auth-control[ x₃ , x₄ ▷ x₅ ]
  with x ≟ₚ x₃
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₁ ≟ₛ x₄
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x₂ ≟ᶜ x₅
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
auth-control[ x , x₁ ▷ x₂ ] ≟ˡ delay[ x₃ ] = no (λ ())

delay[ x ] ≟ˡ auth-join[ x₁ , x₂ ↔ x₃ ] = no (λ ())
delay[ x ] ≟ˡ join[ x₁ ↔ x₂ ] = no (λ ())
delay[ x ] ≟ˡ auth-divide[ x₁ , x₂ ▷ x₃ , x₄ ] = no (λ ())
delay[ x ] ≟ˡ divide[ x₁ ▷ x₂ , x₃ ] = no (λ ())
delay[ x ] ≟ˡ auth-donate[ x₁ , x₂ ▷ᵈ x₃ ] = no (λ ())
delay[ x ] ≟ˡ donate[ x₁ ▷ᵈ x₂ ] = no (λ ())
delay[ x ] ≟ˡ auth-destroy[ x₁ , xs , x₂ ] = no (λ ())
delay[ x ] ≟ˡ destroy[ x₁ ] = no (λ ())
delay[ x ] ≟ˡ advertise[ x₁ ] = no (λ ())
delay[ x ] ≟ˡ auth-commit[ x₁ , x₂ , x₃ ] = no (λ ())
delay[ x ] ≟ˡ auth-init[ x₁ , x₂ , x₃ ] = no (λ ())
delay[ x ] ≟ˡ init[ x₁ , x₂ ] = no (λ ())
delay[ x ] ≟ˡ split[ x₁ ] = no (λ ())
delay[ x ] ≟ˡ auth-rev[ x₁ , x₂ ] = no (λ ())
delay[ x ] ≟ˡ put[ x₁ , x₂ , x₃ ] = no (λ ())
delay[ x ] ≟ˡ withdraw[ x₁ , x₂ , x₃ ] = no (λ ())
delay[ x ] ≟ˡ auth-control[ x₁ , x₂ ▷ x₃ ] = no (λ ())
delay[ x ] ≟ˡ delay[ x₁ ]
  with x ≟ℕ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
