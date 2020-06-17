module BitML.Example.Setup where

open import Data.Product       using (_,_)
open import Data.List          using ([_]; [])
open import Data.List.NonEmpty using (List⁺; _∷_)

open import Prelude.DecEq

data Participant : Set where
  A B : Participant
unquoteDecl DecEqₚ = DERIVE DecEq [ quote Participant , DecEqₚ ]

Honest : List⁺ Participant
Honest = A ∷ []
