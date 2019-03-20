------------------------------------------------------------------------
-- Configurations.
------------------------------------------------------------------------

module Semantics.Configurations.Examples where

open import Level        using (0ℓ)
open import Function     using (_∋_)
open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_; [_]; _++_ ; map; length; filter; zip)
open import Data.Fin     using ()
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Relation.Nullary.Decidable            using (True; fromWitness; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

--------------------------------------------------------------------------------

open import ExampleSetup using (Participant; _≟ₚ_; Honest; A; B)

open import Utilities.Lists

open import Types                            Participant _≟ₚ_ Honest
open import BitML.Types                      Participant _≟ₚ_ Honest
open import BitML.Examples
open import Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

ex-cs : ∃[ v ] ∃[ vs ] Contracts v vs
ex-cs = 1 , [] , [ withdraw A ]

∃ex-ad : ∃[ v ] ∃[ vsᶜ ] ∃[ vsᵛ ] ∃[ vsᵖ ] Advertisement v vsᶜ vsᵛ vsᵖ
∃ex-ad = 5 , [ 100 ] , [ 100 ] , 2 ∷ 3 ∷ [] , ex-ad

-- empty
_ : Configuration [] [] []
_ = ∅ᶜ

-- advertisements
_ : Configuration [ 5 , [ 100 ] , [ 100 ] , 2 ∷ 3 ∷ [] , ex-ad ] [] []
_ = ` ex-ad

-- active contracts
_ : Configuration [] [ 1 , [] , [ withdraw A ] ] []
_ = ⟨ ex-contracts₁ , 1 ⟩ᶜ

-- deposits
_ : Configuration [] [] (A has 4 ∷ [ A has 6 ])
_ = ⟨ A , 4 ⟩ᵈ ∣∣ ⟨ A , 6 ⟩ᵈ

-- authorized actions

-- 1. donate
_ : Configuration′ ([] , []) ([] , []) ([ B has 55 ] , [ A has 55 ])
_ = A auth[ Action A [] [] [ 55 ] [ B has 55 ] ∋
            0ᶠ ▷ᵈ B
          ]

-- 2. divide
_ : Configuration′ ([] , []) ([] , []) (A has 33 ∷ A has 67 ∷ [] , [ A has 100 ])
_ = A auth[ Action A [] [] [ 100 ] (A has 33 ∷ A has 67 ∷ []) ∋
            0ᶠ ▷ 33 , 67
          ]

-- 3. join
_ : Configuration′ ([] , []) ([] , []) ([ A has 100 ] , A has 33 ∷ A has 67 ∷ [])
_ = A auth[ Action A [] [] (33 ∷ 67 ∷ []) [ A has 100 ] ∋
            0ᶠ ↔ sucᶠ 0ᶠ
          ]

-- 4. secret
_ : Configuration′ ([] , [ ∃ex-ad ]) ([] , []) ([] , [])
_ = A auth[ ♯▷ ex-ad ]

-- 5. spend
_ : Configuration′ ([] , [ ∃ex-ad ]) ([] , []) ([] , [ A has 2 ])
_ = A auth[ Action A [ ∃ex-ad ] [] [ 2 ] [] ∋
            ex-ad ▷ˢ 0ᶠ
          ]

-- 6. take branch
_ : Configuration′ ([] , []) ([] , [ 5 , [ 100 ] , ex-contracts₃ ]) ([] , [])
_ = A auth[ ex-contracts₃ ▷ᵇ 0ᶠ ]

-- 7. combination
Γ₁ : Configuration [ ∃ex-ad ]
                   [ ex-cs ]
                   []
Γ₁ = ` ex-ad ∣∣ ⟨ ex-contracts₁ , 1 ⟩ᶜ

Γ₂ : Configuration [ ∃ex-ad ]
                   [ ex-cs ]
                   [ A has 1 ]
Γ₂ = Γ₁ ∣∣ ⟨ A , 1 ⟩ᵈ

Γ₃ : Configuration [ ∃ex-ad ]
                   [ ex-cs ]
                   (A has 1 ∷ A has 2 ∷ [])
Γ₃ = Γ₂ ∣∣ ⟨ A , 2 ⟩ᵈ

Γ₄ : Configuration [ ∃ex-ad ]
                   [ ex-cs ]
                   [ A has 3 ]
Γ₄ = Γ₃
  ∣∣ A auth[ Action A [] [] (1 ∷ 2 ∷ []) [ A has 3 ] ∋
             0ᶠ ↔ sucᶠ 0ᶠ
           ]∶- refl & refl & refl

Γ₅ : Configuration [ ∃ex-ad ]
                   [ ex-cs ]
                   []
Γ₅ = Γ₄
  ∣∣ A auth[ Action A [ ∃ex-ad ] [] [ 3 ] [] ∋
             ex-ad ▷ˢ sucᶠ 0ᶠ
           ]∶- refl & refl & refl


-- secrets
_ : Configuration [] [] []
_ = (A ∶ "qwerty" ♯ 6)

_ : Configuration [] [] []
_ = ⟨ A ∶ "qwerty" ♯ inj₁ 6 ⟩

_ : Configuration [] [] []
_ = ⟨ A ∶ "qwerty" ♯ inj₂ impossible ⟩
  where postulate impossible : ⊥
