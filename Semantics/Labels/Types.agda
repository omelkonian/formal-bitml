------------------------------------------------------------------------
-- Types of labels.
------------------------------------------------------------------------

open import Data.Product using (Σ; Σ-syntax; proj₂)
open import Data.Nat     using (ℕ; _>_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.List    using (List; length)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Semantics.Labels.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists

open import Types                            Participant _≟ₚ_ Honest
open import BitML.Types                      Participant _≟ₚ_ Honest
open import Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

DepositIndex : Set
DepositIndex = ℕ

data Label : Set where

  ---------------
  -- empty label (some transitions do not emit anything)
  empty : Label

  --------
  -- join

  -- A:x,y
  auth-join[_,_↔_] : Participant → DepositIndex → DepositIndex → Label
  -- join(x,y)
  join[_↔_] : DepositIndex → DepositIndex → Label

  ----------
  -- divide

  -- A:x,v,v'
  auth-divide[_,_▷_,_] : Participant → DepositIndex → Value → Value → Label
  -- divide(x,v,v')
  divide[_▷_,_] : DepositIndex → Value → Value → Label

  ----------
  -- donate

  -- A:x,B
  auth-donate[_,_▷ᵈ_] : Participant → DepositIndex → Participant → Label
  -- donate(x,B)
  donate[_▷ᵈ_] : DepositIndex → Participant → Label

  -----------
  -- destroy

  -- A:x,j
  auth-destroy[_,_] : Participant → DepositIndex → Label
  -- destroy(x)
  destroy[_] : DepositIndex → Label

  -------------
  -- advertise

  -- advertise({G}C)
  advertise[_] : ∃Advertisement → Label

  --------
  -- init

  -- A:{G}C,Δ
  auth-commit[_,_,_] : Participant → ∃Advertisement → List CommittedSecret → Label
  -- A:{G}C,x
  auth-init[_,_,_] : Participant → ∃Advertisement → DepositIndex → Label
  -- init(G,C)
  init[_] : ∃Advertisement → Label

  --------
  -- split

  -- split(y)
  split : Label

  --------------
  -- auth-reveal

  -- A:a
  auth-rev[_,_] : Participant → Secret → Label

  -------------
  -- put-reveal

  -- put(x,a,y)
  put[_,_] : Values → Secrets → Label

  ------------
  -- withdraw

  -- withdraw(A,v,y)
  withdraw[_,_] : Participant → Value → Label

  ---------------
  -- auth-control

  -- A:x,D
  auth-control[_,_▷ᵇ_] : Participant → (c : ∃Contracts) → Index (proj₂ c) → Label

  ---------
  -- delay

  -- δ
  delay[_] : Time → Label

Labels : Set
Labels = List Label

authDecoration : Label → Maybe Participant
authDecoration auth-join[ p , _ ↔ _ ]       = just p
authDecoration auth-divide[ p , _ ▷ _ , _ ] = just p
authDecoration auth-donate[ p , _ ▷ᵈ _ ]    = just p
authDecoration auth-destroy[ p , _ ]        = just p
authDecoration auth-commit[ p , _ , _ ]     = just p
authDecoration auth-init[ p , _ , _ ]       = just p
authDecoration auth-rev[ p , _ ]            = just p
authDecoration auth-control[ p , _ ▷ᵇ _ ]   = just p
authDecoration _                            = nothing
