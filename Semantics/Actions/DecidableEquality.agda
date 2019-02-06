------------------------------------------------------------------------
-- Decidable equality for actions
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Data.Nat     using (ℕ; _≟_; _>_; _+_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _,_)
open import Data.List    using (List; []; _∷_; [_]; _++_; map; length)
open import Data.Fin     using ()
  renaming (zero to 0ᶠ; suc to sucᶠ; _≟_ to _≟ᶠ_)

open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Decidable using (True; False; fromWitness)
open import Relation.Binary            using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

module Semantics.Actions.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

import Data.Set' as SET
open import Utilities.Lists

open import Types                   Participant _≟ₚ_ Honest
open import BitML.Types             Participant _≟ₚ_ Honest
open import BitML.DecidableEquality Participant _≟ₚ_ Honest
open import Semantics.Actions.Types Participant _≟ₚ_ Honest

------------------------------------------------------------------------

-- Actions.
_≟ᵃ_ : ∀ {p ads cs vs ds} → Decidable {A = Action p ads cs vs ds} _≡_

(♯▷ ad) ≟ᵃ (♯▷ .ad)   = yes refl
(♯▷ ad) ≟ᵃ (.ad ▷ˢ i) = no λ ()

(ad ▷ˢ i) ≟ᵃ (♯▷ .ad) = no λ ()
(ad ▷ˢ i) ≟ᵃ (.ad ▷ˢ i′) with i ≟ᶠ i′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

(c ▷ᵇ i) ≟ᵃ (.c ▷ᵇ i′) with i ≟ᶠ i′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

(x ↔ y) ≟ᵃ (x′ ↔ y′)
  with x ≟ᶠ x′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with y ≟ᶠ y′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(x ↔ y) ≟ᵃ (i ▷ v₁ , v₂) = no λ ()
(x ↔ y) ≟ᵃ (i ▷ᵈ p′)     = no λ ()
(x ↔ y) ≟ᵃ destroy i     = no λ ()

(i ▷ v₁ , v₂) ≟ᵃ (i′ ▷ v₁′ , v₂′)
  with i ≟ᶠ i′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with v₁ SETₙ.≣ v₁′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with v₂ SETₙ.≣ v₂′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(i ▷ v₁ , v₂) ≟ᵃ (x ↔ y)    = no λ ()
(i ▷ v₁ , v₂) ≟ᵃ (i₁ ▷ᵈ p′) = no λ ()
(i ▷ v₁ , v₂) ≟ᵃ destroy i₁ = no λ ()

(i ▷ᵈ a) ≟ᵃ (i′ ▷ᵈ b)
  with i ≟ᶠ i′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with a SETₚ.≣ b
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(i ▷ᵈ p′) ≟ᵃ (x ↔ y)        = no λ ()
(i ▷ᵈ p′) ≟ᵃ (i₁ ▷ v₁ , v₂) = no λ ()
(i ▷ᵈ p′) ≟ᵃ destroy i₁     = no λ ()

destroy i ≟ᵃ destroy i′
  with i ≟ᶠ i′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
destroy i ≟ᵃ (x ↔ y)        = no λ ()
destroy i ≟ᵃ (i₁ ▷ v₁ , v₂) = no λ ()
destroy i ≟ᵃ (i₁ ▷ᵈ p′)     = no λ ()
