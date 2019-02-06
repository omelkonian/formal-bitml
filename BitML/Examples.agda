------------------------------------------------------------------------
-- Examples of BitML contracts/advertisements.
------------------------------------------------------------------------

module BitML.Examples where

open import Data.List     using (List; []; _∷_; [_])
open import Data.List.Any using (here; there)

open import Relation.Binary.PropositionalEquality using (refl)

--------------------------------------------------------------------------------

open import Utilities.Lists

open import ExampleSetup using (Participant; _≟ₚ_; Honest; A; B)
open import Types       Participant _≟ₚ_ Honest
open import BitML.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

ex-contracts₁ : Contracts 1 []
ex-contracts₁ = withdraw A ∙

ex-contracts₂ : Contracts 5 []
ex-contracts₂ = (A ∶ withdraw A)
              ⊕ (put [] &reveal [] if `True ⇒ withdraw {5} A
                 ∶- sound-put & (λ {x} z → z) & refl)
              ∙

ex-contracts₃ : Contracts 5 [ 100 ]
ex-contracts₃ = (put [ 100 ] &reveal [] if `True ⇒ withdraw {105} A
                 ∶- sound-put & (λ {x} z → z) & refl) ∙

ex-contracts₄ : Contracts 5 []
ex-contracts₄ = (A ∶ withdraw {5} B)
              ⊕ (B ∶ split ( (2 ⊸ withdraw {2} A)
                           ⊕ (3 ⊸ after 100 ∶ withdraw {3} B)
                           ⊕ (0 ⊸ put [ 10 ]
                                  &reveal []
                                  if `True
                                  ⇒ (A ∶ withdraw {10} B)
                                  ∶- sound-put & (λ {x} z → z) & refl)
                           ∙))
              ∙

ex-ad : Advertisement 5 [ 100 ] (200 ∷ 100 ∷ [])
ex-ad = ⟨ B :! 200 ∣ A :! 100  ⟩ ex-contracts₃
        ∶- sound-≾
        &  λ{ {x} (here px)                  → here px
            ; {x} (there (here px))          → there (here px)
            ; {x} (there (there (here px)))  → there (here px)
            ; {x} (there (there (there ())))
            }
