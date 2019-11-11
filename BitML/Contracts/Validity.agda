------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------

open import Function using (_∘_)

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Nat     using (_>_)
open import Data.List    using (List; length; _++_)

open import Data.List.Relation.Unary.All                   using (All; all)
open import Data.List.Relation.Unary.Unique.Propositional  using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Product   using (_×-dec_)
open import Relation.Binary            using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate.Base

module BitML.Contracts.Validity
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types   Participant _≟ₚ_ Honest
open import BitML.Contracts.Helpers Participant _≟ₚ_ Honest

ValidAdvertisement : Advertisement → Set
ValidAdvertisement (⟨ G ⟩ C) =
    -- (i) names in G are distinct
    Unique (namesᵖ G)

    -- (ii) each name in C appears in G
  × namesᶜˢ C ⊆ namesᵖ G

    -- (iii) the names in put_&reveal_ are distinct and secrets in `if ...` appear in `reveal ...`
  × All (λ{ (xs , as , p) → Unique xs × (secretsᵖʳ p ⊆ as)}) (putComponentsᶜˢ C)

    -- (iv) each participant has a persistent deposit in G
  × participantsᵖ G ++ participantsᶜˢ C ⊆ persistentParticipantsᵖ G

validAd? : ∀ (ad : Advertisement) → Dec (ValidAdvertisement ad)
validAd? (⟨ G ⟩ C) =
        SETₛ.unique? (namesᵖ G)
  ×-dec namesᶜˢ C SETₛ.⊆? namesᵖ G
  ×-dec all (λ{ (xs , as , p) → SETₛ.unique? xs ×-dec (secretsᵖʳ p SETₛ.⊆? as)}) (putComponentsᶜˢ C)
  ×-dec participantsᵖ G ++ participantsᶜˢ C SETₚ.⊆? persistentParticipantsᵖ G
