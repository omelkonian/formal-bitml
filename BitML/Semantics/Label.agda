-----------------------------------------------------------------------
-- Types of labels.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

open import BitML.BasicTypes

module BitML.Semantics.Label
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Semantics.Action Participant Honest

--------------------------------------------------------------------------------

data Label : Set where

  --------
  -- join

  -- A:x,y
  auth-join[_,_↔_] : Participant → Id → Id → Label
  -- join(x,y)
  join[_↔_] : Id → Id → Label

  ----------
  -- divide

  -- A:x,v,v'
  auth-divide[_,_▷_,_] : Participant → Id → Value → Value → Label
  -- divide(x,v,v')
  divide[_▷_,_] : Id → Value → Value → Label

  ----------
  -- donate

  -- A:x,B
  auth-donate[_,_▷ᵈ_] : Participant → Id → Participant → Label
  -- donate(x,B)
  donate[_▷ᵈ_] : Id → Participant → Label

  -----------
  -- destroy

  -- A:x,j
  auth-destroy[_,_,_] : Participant → (xs : Ids) → Index xs → Label
  -- destroy(x)
  destroy[_] : Ids → Label

  -------------
  -- advertise

  -- advertise({G}C)
  advertise[_] : Advertisement → Label

  --------
  -- init

  -- A:{G}C,Δ
  auth-commit[_,_,_] : Participant → Advertisement → List (Secret × Maybe ℕ) → Label
  -- A:{G}C,x
  auth-init[_,_,_] : Participant → Advertisement → Id → Label
  -- init(G,C)
  init[_,_] : Precondition → Contracts → Label

  --------
  -- split

  -- split(y)
  split[_] : Id → Label

  --------------
  -- auth-reveal

  -- A:a
  auth-rev[_,_] : Participant → Secret → Label

  -------------
  -- put-reveal

  -- put(x,a,y)
  put[_,_,_] : Ids → Secrets → Id → Label

  ------------
  -- withdraw

  -- withdraw(A,v,y)
  withdraw[_,_,_] : Participant → Value → Id → Label

  ---------------
  -- auth-control

  -- A:x,D
  auth-control[_,_▷_] : Participant → Id → Contract → Label

  ---------
  -- delay

  -- δ
  delay[_] : Time → Label

unquoteDecl DecEq-Label = DERIVE DecEq [ quote Label , DecEq-Label ]

Labels : Set
Labels = List Label

variable
  α α′ α″ : Label
  αs αs′ : Labels

cv : Label → Maybe Id
cv put[ _ , _ , y ]      = just y
cv withdraw[ _ , _ , y ] = just y
cv split[ y ]            = just y
cv _                     = nothing


authDecoration : Label → Maybe Participant
authDecoration auth-join[ p , _ ↔ _ ]       = just p
authDecoration auth-divide[ p , _ ▷ _ , _ ] = just p
authDecoration auth-donate[ p , _ ▷ᵈ _ ]    = just p
authDecoration auth-destroy[ p , _ , _ ]    = just p
authDecoration auth-commit[ p , _ , _ ]     = just p
authDecoration auth-init[ p , _ , _ ]       = just p
authDecoration auth-rev[ p , _ ]            = just p
authDecoration auth-control[ p , _ ▷ _ ]   = just p
authDecoration _                            = nothing
