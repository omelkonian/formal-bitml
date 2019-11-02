module BitML.Example.Setup where

open import Data.Nat            using (_>_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product        using (Σ; Σ-syntax; _,_)
open import Data.List           using (List; [_]; length)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Participant : Set where
  A : Participant
  B : Participant

_≟ₚ_ : Decidable {A = Participant} _≡_
A ≟ₚ A = yes refl
A ≟ₚ B = no λ ()
B ≟ₚ A = no λ ()
B ≟ₚ B = yes refl

Honest : Σ[ ps ∈ List Participant ] (length ps > 0)
Honest = [ A ] , ≤-refl
