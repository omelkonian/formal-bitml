------------------------------------------------------------------------
-- Examples of actions.
------------------------------------------------------------------------

module BitML.Semantics.Actions.Examples where

open import Function     using (_∋_)
open import Data.Nat     using (ℕ; _≟_; _>_; _+_)
open import Data.Product using (_,_)
open import Data.List    using (List; []; _∷_; [_]; _++_; map; length)
open import Data.Fin     using ()
  renaming (zero to 0ᶠ; suc to sucᶠ)

open import Relation.Nullary.Decidable            using (fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)

open import Prelude.Lists
open import BitML.BasicTypes

open import BitML.Contracts.Types         Participant _≟ₚ_ Honest
open import BitML.Contracts.Examples
open import BitML.Semantics.Actions.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

-- donate
_ : Action A Iᵃᶜ[ [] , [] , 0 ∷ 10 ∷ 20 ∷ [] , [ B has 10 ] ]
_ = sucᶠ 0ᶠ ▷ᵈ B

-- divide
_ : Action A Iᵃᶜ[ [] , [] , [ 100 ] , A has 33 ∷ A has 67 ∷ [] ]
_ = 0ᶠ ▷ 33 , 67

-- join
_ : Action A Iᵃᶜ[ [] , [] , 33 ∷ 67 ∷ [] , [ A has 100 ] ]
_ = 0ᶠ ↔ sucᶠ 0ᶠ

-- secret
_ : Action A Iᵃᶜ[ [ Iᶜ[ 5 , [ 100 ] ] , Iᵖ[ [ 100 ] , 2 ∷ 3 ∷ [] ] , ex-ad ] , [] , [] , [] ]
_ = ♯▷ ex-ad

-- spend
_ : Action A Iᵃᶜ[ [ Iᶜ[ 5 , [ 100 ] ] , Iᵖ[ [ 100 ] , 2 ∷ 3 ∷ [] ] , ex-ad ] , [] , [ 3 ] , [] ]
_ = ex-ad ▷ˢ sucᶠ 0ᶠ

-- take branch
_ : Action A Iᵃᶜ[ [] , [ Iᶜ[ 5 , [ 100 ] ] , ex-contracts₃ ] , [] , [] ]
_ = ex-contracts₃ ▷ᵇ 0ᶠ

-- destroy
_ : Action A Iᵃᶜ[ [] , [] , [ 100 ] , [] ]
_ = destroy 0ᶠ
