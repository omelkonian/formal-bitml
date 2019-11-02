------------------------------------------------------------------------
-- Configurations.
------------------------------------------------------------------------

module BitML.Semantics.Configurations.Examples where

open import Level        using (0ℓ)
open import Function     using (_∋_)
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (just; nothing)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
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

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)

open import Prelude.Lists

open import BitML.BasicTypes                       Participant _≟ₚ_ Honest
open import BitML.Contracts.Types                  Participant _≟ₚ_ Honest
open import BitML.Contracts.Examples
open import BitML.Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Helpers Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

ex-cs : Contracts Iᶜ[ 1 , [] ]
ex-cs = [ withdraw A ]

∃ex-cs : ∃[ ci ] Contracts ci
∃ex-cs = Iᶜ[ 1 , [] ] , [ withdraw A ]

∃ex-ad : ∃[ ci ] ∃[ pi ] Advertisement ci pi
∃ex-ad = Iᶜ[ 5 , [ 100 ] ] , Iᵖ[ [ 100 ] , 2 ∷ 3 ∷ [] ] , ex-ad

-- empty
_ : Configuration Iᶜᶠ[ [] , [] , [] ]
_ = ∅ᶜ

-- advertisements
_ : Configuration Iᶜᶠ[ [ ∃ex-ad ] , [] , [] ]
_ = ` ex-ad

-- active contracts
_ : Configuration Iᶜᶠ[ [] , [ ∃ex-cs ] , [] ]
_ = ⟨ ex-contracts₁ ⟩ᶜ

-- deposits
_ : Configuration Iᶜᶠ[ [] , [] , A has 4 ∷ [ A has 6 ] ]
_ = ⟨ A , 4 ⟩ᵈ ∣∣ ⟨ A , 6 ⟩ᵈ

-- authorized actions

-- 1. donate
_ : Configuration′ Iᶜᶠ[ [] & [] , [] & [] , [ B has 55 ] & [ A has 55 ] ]
_ = A auth[ Action A Iᵃᶜ[ [] , [] , [ 55 ] , [ B has 55 ] ] ∋
            0ᶠ ▷ᵈ B
          ]

-- 2. divide
_ : Configuration′ Iᶜᶠ[ [] & [] , [] & [] , (A has 33 ∷ A has 67 ∷ []) & [ A has 100 ] ]
_ = A auth[ Action A Iᵃᶜ[ [] , [] , [ 100 ] , A has 33 ∷ A has 67 ∷ [] ] ∋
            0ᶠ ▷ 33 , 67
          ]

-- 3. join
_ : Configuration′ Iᶜᶠ[ [] & [] , [] & [] , [ A has 100 ] & (A has 33 ∷ A has 67 ∷ []) ]
_ = A auth[ Action A Iᵃᶜ[ [] , [] , 33 ∷ 67 ∷ [] , [ A has 100 ] ] ∋
            0ᶠ ↔ sucᶠ 0ᶠ
          ]

-- 4. secret
_ : Configuration′ Iᶜᶠ[ [] & [ ∃ex-ad ] , [] & [] , [] & [] ]
_ = A auth[ ♯▷ ex-ad ]

-- 5. spend
_ : Configuration′ Iᶜᶠ[ [] & [ ∃ex-ad ] , [] & [] , [] & [ A has 2 ] ]
_ = A auth[ Action A Iᵃᶜ[ [ ∃ex-ad ] , [] , [ 2 ] , [] ] ∋
            ex-ad ▷ˢ 0ᶠ
          ]

-- 6. take branch
_ : Configuration′ Iᶜᶠ[ [] & [] , [] & [ Iᶜ[ 5 , [ 100 ] ] , ex-contracts₃ ] , [] & [] ]
_ = A auth[ ex-contracts₃ ▷ᵇ 0ᶠ ]

-- 7. combination
Γ₁ : Configuration Iᶜᶠ[ [ ∃ex-ad ] , [ ∃ex-cs ] , [] ]
Γ₁ = ` ex-ad ∣∣ ⟨ ex-contracts₁ ⟩ᶜ

Γ₂ : Configuration Iᶜᶠ[ [ ∃ex-ad ] , [ ∃ex-cs ] , [ A has 1 ] ]
Γ₂ = Γ₁ ∣∣ ⟨ A , 1 ⟩ᵈ

Γ₃ : Configuration Iᶜᶠ[ [ ∃ex-ad ] , [ ∃ex-cs ] , A has 1 ∷ A has 2 ∷ [] ]
Γ₃ = Γ₂ ∣∣ ⟨ A , 2 ⟩ᵈ

Γ₄ : Configuration Iᶜᶠ[ [ ∃ex-ad ] , [ ∃ex-cs ] , [ A has 3 ] ]
Γ₄ = Γ₃
  ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , 1 ∷ 2 ∷ [] , [ A has 3 ] ] ∋
             0ᶠ ↔ sucᶠ 0ᶠ
           ]∶- refl & refl & refl & refl & refl & refl

Γ₅ : Configuration Iᶜᶠ[ [ ∃ex-ad ] , [ ∃ex-cs ] , [] ]
Γ₅ = Γ₄
  ∣∣ A auth[ Action A Iᵃᶜ[ [ ∃ex-ad ] , [] , [ 3 ] , [] ] ∋
             ex-ad ▷ˢ sucᶠ 0ᶠ
           ]∶- refl & refl & refl & refl & refl & refl


-- secrets
_ : Configuration Iᶜᶠ[ [] , [] , [] ]
_ = (A ∶ "qwerty" ♯ 6)

_ : Configuration Iᶜᶠ[ [] , [] , [] ]
_ = ⟨ A ∶ "qwerty" ♯ just 6 ⟩

_ : Configuration Iᶜᶠ[ [] , [] , [] ]
_ = ⟨ A ∶ "qwerty" ♯ nothing ⟩
