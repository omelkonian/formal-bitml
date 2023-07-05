module BitML.Example.Setup where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq

data Participant : Type where
  A B : Participant
unquoteDecl DecEqₚ = DERIVE DecEq [ quote Participant , DecEqₚ ]

Honest : List⁺ Participant
Honest = A ∷ []
