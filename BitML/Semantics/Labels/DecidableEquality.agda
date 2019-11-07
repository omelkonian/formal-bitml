------------------------------------------------------------------------
-- Decidable equality for labels.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat     using (_>_)
open import Data.Product using (Σ; Σ-syntax)
open import Data.List    using (List; length)

open import Relation.Nullary           using (yes; no)
open import Relation.Binary            using (Decidable)

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

-- Actions.
_≟ˡ_ : Decidable {A = Label} _≡_
l ≟ˡ l′ = {!!}
