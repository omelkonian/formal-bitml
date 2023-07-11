-----------------------------------------------------------------------
-- Types of labels.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Membership

open import BitML.BasicTypes

module BitML.Semantics.Label (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Contracts.Types ⋯
open import BitML.Semantics.Action ⋯

data Label : Type where
  auth-join⦅_,_↔_⦆ : Participant → Id → Id → Label -- A:x,y
  join⦅_↔_⦆ : Id → Id → Label -- join(x,y)

  auth-divide⦅_,_▷_,_⦆ : Participant → Id → Value → Value → Label -- A:x,v,v'
  divide⦅_▷_,_⦆ : Id → Value → Value → Label -- divide(x,v,v')

  auth-donate⦅_,_▷ᵈ_⦆ : Participant → Id → Participant → Label -- A:x,B
  donate⦅_▷ᵈ_⦆ : Id → Participant → Label -- donate(x,B)

  auth-destroy⦅_,_,_⦆ : Participant → (xs : Ids) → Index xs → Label -- A:x,j
  destroy⦅_⦆ : Ids → Label -- destroy(x)

  advertise⦅_⦆ : Ad → Label -- advertise({G}C)

  auth-commit⦅_,_,_⦆ : Participant → Ad → List (Secret × Maybe ℕ) → Label -- A:{G}C,Δ
  auth-init⦅_,_,_⦆ : Participant → Ad → Id → Label -- A:{G}C,x
  init⦅_,_⦆ : Precondition → Contract → Label -- init(G,C)

  split⦅_⦆ : Id → Label -- split(y)
  auth-rev⦅_,_⦆ : Participant → Secret → Label -- A:a
  put⦅_,_,_⦆ : Ids → Secrets → Id → Label -- put(x,a,y)
  withdraw⦅_,_,_⦆ : Participant → Value → Id → Label -- withdraw(A,v,y)

  auth-control⦅_,_▷_⦆ : Participant → Id → Branch → Label -- A:x,D

  delay⦅_⦆ : Time → Label -- δ

unquoteDecl DecEq-Label = DERIVE DecEq [ quote Label , DecEq-Label ]

Labels = List Label

variable
  α α′ α″ : Label
  αs αs′ : Labels

cv : Label → Maybe Id
cv = λ where
  put⦅ _ , _ , y ⦆      → just y
  withdraw⦅ _ , _ , y ⦆ → just y
  split⦅ y ⦆            → just y
  _                     → nothing

authDecoration : Label → Maybe Participant
authDecoration = λ where
  auth-join⦅ p , _ ↔ _ ⦆       → just p
  auth-divide⦅ p , _ ▷ _ , _ ⦆ → just p
  auth-donate⦅ p , _ ▷ᵈ _ ⦆    → just p
  auth-destroy⦅ p , _ , _ ⦆    → just p
  auth-commit⦅ p , _ , _ ⦆     → just p
  auth-init⦅ p , _ , _ ⦆       → just p
  auth-rev⦅ p , _ ⦆            → just p
  auth-control⦅ p , _ ▷ _ ⦆    → just p
  _                            → nothing

mentionedAd : Label → Maybe Ad
mentionedAd = λ where
  advertise⦅ ad ⦆           → just ad
  auth-commit⦅ _ , ad , _ ⦆ → just ad
  auth-init⦅ _ , ad , _ ⦆   → just ad
  init⦅ g , c ⦆             → just $ ⟨ g ⟩ c
  _                         → nothing

focusOn : Ad → List Label → List Label
focusOn ad = filter (λ l → ad ∈? mentionedAd l)
