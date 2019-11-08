------------------------------------------------------------------------
-- Types of configurations.
------------------------------------------------------------------------

open import Data.Maybe   using (Maybe)
open import Data.Nat     using (ℕ; _>_)
open import Data.Product using (Σ-syntax)
open import Data.List    using (List; length; foldl; []; _∷_)

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types                     Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types             Participant _≟ₚ_ Honest

-------------------------------------------------------------------

data Configuration : Set where

  -- empty
  ∅ᶜ : Configuration

  -- contract advertisement
  `_ : Advertisement → Configuration

  -- active contract
  ⟨_,_⟩at_ : Contracts → Value → Id → Configuration

  -- deposit redeemable by a participant
  ⟨_has_⟩at_ : Participant → Value → Id → Configuration

  -- authorization to perform an action
  _auth[_] : Participant → Action → Configuration

  -- committed secret
  ⟨_∶_♯_⟩ : Participant → Secret → Maybe ℕ → Configuration

  -- revealed secret
  _∶_♯_ : Participant → Secret → ℕ → Configuration

  -- parallel composition
  _∣_ : Configuration → Configuration → Configuration

variable
  Γ Γ′ Δ Δ′ L L′ M M′ : Configuration

||_ : List Configuration → Configuration
-- ||_ = foldl _∣_ ∅ᶜ
|| [] = ∅ᶜ
|| (Γ ∷ []) = Γ
|| (Γ ∷ Γs) = Γ ∣ || Γs

record TimedConfiguration : Set where
  constructor _at_
  field
    cfg  : Configuration
    time : Time
open TimedConfiguration public

infix  9 ⟨_,_⟩at_
infix  8 ⟨_has_⟩at_
infix  6 _auth[_]
infix  5 ||_
infixl 4 _∣_
