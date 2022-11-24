-----------------------------------------------------------------------
-- Types of labels.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Sets
open import Prelude.ToList

open import BitML.BasicTypes

module BitML.Semantics.Label
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Semantics.Action Participant Honest

data Label : Set where
  auth-join⦅_,_↔_⦆ : Participant → Id → Id → Label -- A:x,y
  join⦅_↔_⦆ : Id → Id → Label -- join(x,y)

  auth-divide⦅_,_▷_,_⦆ : Participant → Id → Value → Value → Label -- A:x,v,v'
  divide⦅_▷_,_⦆ : Id → Value → Value → Label -- divide(x,v,v')

  auth-donate⦅_,_▷ᵈ_⦆ : Participant → Id → Participant → Label -- A:x,B
  donate⦅_▷ᵈ_⦆ : Id → Participant → Label -- donate(x,B)

  auth-destroy⦅_,_,_⦆ : Participant → (xs : Ids) → Index (toList xs) → Label -- A:x,j
  destroy⦅_⦆ : Ids → Label -- destroy(x)

  advertise⦅_⦆ : Advertisement → Label -- advertise({G}C)

  auth-commit⦅_,_,_⦆ : Participant → Advertisement → List (Secret × Maybe ℕ) → Label -- A:{G}C,Δ
  auth-init⦅_,_,_⦆ : Participant → Advertisement → Id → Label -- A:{G}C,x
  init⦅_,_⦆ : Precondition → Contracts → Label -- init(G,C)

  split⦅_⦆ : Id → Label -- split(y)
  auth-rev⦅_,_⦆ : Participant → Secret → Label -- A:a
  put⦅_,_,_⦆ : Ids → Secrets → Id → Label -- put(x,a,y)
  withdraw⦅_,_,_⦆ : Participant → Value → Id → Label -- withdraw(A,v,y)

  auth-control⦅_,_▷_⦆ : Participant → Id → Contract → Label -- A:x,D

  delay⦅_⦆ : Time → Label -- δ

unquoteDecl DecEq-Label = DERIVE DecEq [ quote Label , DecEq-Label ]

Labels : Set
Labels = List Label

variable
  α α′ α″ : Label
  αs αs′ : Labels

cv : Label → Maybe Id
cv put⦅ _ , _ , y ⦆      = just y
cv withdraw⦅ _ , _ , y ⦆ = just y
cv split⦅ y ⦆            = just y
cv _                     = nothing

authDecoration : Label → Maybe Participant
authDecoration auth-join⦅ p , _ ↔ _ ⦆       = just p
authDecoration auth-divide⦅ p , _ ▷ _ , _ ⦆ = just p
authDecoration auth-donate⦅ p , _ ▷ᵈ _ ⦆    = just p
authDecoration auth-destroy⦅ p , _ , _ ⦆    = just p
authDecoration auth-commit⦅ p , _ , _ ⦆     = just p
authDecoration auth-init⦅ p , _ , _ ⦆       = just p
authDecoration auth-rev⦅ p , _ ⦆            = just p
authDecoration auth-control⦅ p , _ ▷ _ ⦆   = just p
authDecoration _                            = nothing

mentionedAd : Label → Maybe Advertisement
mentionedAd = λ where
  (advertise⦅ ad ⦆) → just ad
  (auth-commit⦅ _ , ad , _ ⦆) → just ad
  (auth-init⦅ _ , ad , _ ⦆) → just ad
  (init⦅ g , c ⦆) → just $ ⟨ g ⟩ c
  _ → nothing

focusOn : Advertisement → List Label → List Label
focusOn ad = filter (λ l → ad ∈? mentionedAd l)
