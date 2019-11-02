------------------------------------------------------------------------
-- Examples of BitML contracts/advertisements.
------------------------------------------------------------------------

module BitML.Contracts.Examples where

open import Data.Unit     using (tt)
open import Data.List     using (List; []; _∷_; [_])
open import Data.List.Any using (here; there)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Relation.Binary.Sublist.Heterogeneous as SB

--------------------------------------------------------------------------------

open import Prelude.Lists

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)
open import BitML.BasicTypes      Participant _≟ₚ_ Honest
open import BitML.Contracts.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

ex-contracts₁ : Contracts Iᶜ[ 1 , [] ]
ex-contracts₁ = withdraw A ∙

ex-contracts₂ : Contracts Iᶜ[ 5 , [] ]
ex-contracts₂ = A ∶ withdraw {Iᶜ[ 5 , _ ]} A
              ⊕ (put [] &reveal [] if `True ⇒ [ withdraw {Iᶜ[ 5 , _ ]} A ]) {p₁ = tt}
              ∙

ex-contracts₃ : Contracts Iᶜ[ 5 , [ 100 ] ]
ex-contracts₃ = (put [ 100 ] &reveal [] if `True ⇒ [ withdraw {Iᶜ[ 105 , _ ]} A ]) {p₁ = tt}
                 ∙

ex-contracts₄ : Contracts Iᶜ[ 5 , [ 10 ] ]
ex-contracts₄ = (A ∶ withdraw {Iᶜ[ 5 , _ ]} B)
              ⊕ (B ∶ split ( (2 ⊸ withdraw {Iᶜ[ 2 , _ ]} A)
                           ⊕ (3 ⊸ after 100 ∶ withdraw {Iᶜ[ 3 , _ ]} B)
                           ⊕ (0 ⊸ (put [ 10 ] &reveal [] if `True ⇒ [ A ∶ withdraw {Iᶜ[ 10 , _ ]} B ]) {p₁ = tt})
                           ∙))
              ∙


-- see BitML paper, Section 2
pay-or-refund : Advertisement Iᶜ[ 1 , [] ] Iᵖ[ [] , 1 ∷ 0 ∷ [] ]
pay-or-refund = ⟨ A :! 1 ∣ B :! 0 ⟩
                  A ∶ withdraw B
                ⊕ B ∶ withdraw A
                ∙
                ∶- sound-≾
                 & (λ { (here px)                                          → here px
                      ; (there (here px))                                  → there (here px)
                      ; (there (there (here px)))                          → here px
                      ; (there (there (there (here px))))                  → there (here px)
                      ; (there (there (there (there (here px)))))          → there (here px)
                      ; (there (there (there (there (there (here px))))))  → here px
                      ; (there (there (there (there (there (there ()))))))
                      })
                 & refl


ex-ad : Advertisement Iᶜ[ 5 , [ 100 ] ] Iᵖ[ [ 100 ] , 2 ∷ 3 ∷ [] ]
ex-ad = ⟨ B :! 2
        ∣ A :! 3   ∶- refl & refl
        ∣ A :? 100 ∶- refl & refl
        ⟩ ex-contracts₃
        ∶- sound-≾
         & (λ { (here px)                          → here px
              ; (there (here px))                  → there (here px)
              ; (there (there (here px)))          → there (here px)
              ; (there (there (there (here px))))  → there (here px)
              ; (there (there (there (there ()))))
              })
         & refl
