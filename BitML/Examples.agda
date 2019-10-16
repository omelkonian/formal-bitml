------------------------------------------------------------------------
-- Examples of BitML contracts/advertisements.
------------------------------------------------------------------------

module BitML.Examples where

open import Data.Unit     using (tt)
open import Data.List     using (List; []; _∷_; [_])
open import Data.List.Any using (here; there)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Relation.Binary.Sublist.Heterogeneous as SB

--------------------------------------------------------------------------------

open import Utilities.Lists

open import Example.Setup using (Participant; _≟ₚ_; Honest; A; B)
open import Types       Participant _≟ₚ_ Honest
open import BitML.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

ex-contracts₁ : Contracts 1 []
ex-contracts₁ = withdraw A ∙

ex-contracts₂ : Contracts 5 []
ex-contracts₂ = A ∶ withdraw {5} A
              ⊕ (put [] &reveal [] if `True ⇒ [ withdraw {5} A ]) {p₁ = tt}
              ∙

ex-contracts₃ : Contracts 5 [ 100 ]
ex-contracts₃ = (put [ 100 ] &reveal [] if `True ⇒ [ withdraw {105} A ]) {p₁ = tt}
                 ∙

ex-contracts₄ : Contracts 5 [ 10 ]
ex-contracts₄ = (A ∶ withdraw {5} B)
              ⊕ (B ∶ split ( (2 ⊸ withdraw {2} A)
                           ⊕ (3 ⊸ after 100 ∶ withdraw {3} B)
                           ⊕ (0 ⊸ (put [ 10 ] &reveal [] if `True ⇒ [ A ∶ withdraw {10} B ]) {p₁ = tt})
                           ∙))
              ∙


-- see BitML paper, Section 2
pay-or-refund : Advertisement 1 [] [] (1 ∷ 0 ∷ [])
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


ex-ad : Advertisement 5 [ 100 ] [ 100 ] (2 ∷ 3 ∷ [])
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
