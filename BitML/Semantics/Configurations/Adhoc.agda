open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.DecLists
open import Prelude.Setoid
open import Prelude.Lists.Collections
open import Prelude.Nary

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Adhoc
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Semantics.Action Participant Honest

data BaseCfg : Set where

  -- empty
  ∅ᶜ : BaseCfg

  -- contract advertisement
  `_ : Advertisement → BaseCfg

  -- active contract
  ⟨_,_⟩at_ : Contracts → Value → Id → BaseCfg

  -- deposit redeemable by a participant
  ⟨_has_⟩at_ : Participant → Value → Id → BaseCfg

  -- authorization to perform an action
  _auth[_] : Participant → Action → BaseCfg

  -- committed secret
  ⟨_∶_♯_⟩ : Participant → Secret → Maybe ℕ → BaseCfg

  -- revealed secret
  _∶_♯_ : Participant → Secret → ℕ → BaseCfg

unquoteDecl DecEqᶜᶠ = DERIVE DecEq [ quote BaseCfg , DecEqᶜᶠ ]

Cfg = List BaseCfg

infix  11 ⟨_,_⟩at_
infix  10 ⟨_has_⟩at_
infix  8 _auth[_]

{-
pattern _∣_ x xs = _∷_ x xs
_∣_ : BaseCfg → Cfg → Cfg
c ∣ cs = c ∷ cs
-}

record _∣_↝_ (A B C : Set) : Set where
  infixr 6 _∣_
  field _∣_ : A → B → C
open _∣_↝_ ⦃ ... ⦄ public

instance
  bar₁ : BaseCfg ∣ BaseCfg ↝ Cfg
  bar₁ ._∣_ b b′ = ⟦ b , b′ ⟧

  bar₂ : BaseCfg ∣ Cfg ↝ Cfg
  bar₂ ._∣_ = _∷_

  bar₃ : Cfg ∣ BaseCfg ↝ Cfg
  bar₃ ._∣_ = _∷ʳ_

  bar₄ : Cfg ∣ Cfg ↝ Cfg
  bar₄ ._∣_ = _++_

{-
record _∣_↝_ (A B C : Set) : Set where
  field bar : A → B → C
  -- _BAR_ = bar
open _∣_↝_ ⦃ ... ⦄ public

-- pattern _∣_ x y = _BAR_ x y
-}

{-
infixr 6 _∣₁_
_∣₁_ : BaseCfg → BaseCfg → Cfg
b ∣₁ b′ = ⟦ b , b′ ⟧

-- bar₂ : BaseCfg → Cfg → Cfg
-- bar₂ = _∷_

-- bar₃ : Cfg → BaseCfg → Cfg
-- bar₃ = _∷ʳ_

-- bar₄ : Cfg → Cfg → Cfg
-- bar₄ = _++_

-- pattern _∣_ = _∣₁_
pattern _∣_ x y = x ∷ y ∷ []
pattern _∣_ x xs = x ∷ xs
open import Data.List using (_∷ʳ′_)
pattern _∣_ xs x = xs ∷ʳ′ x
-- pattern _∣_ xs ys = xs ++ ys
-}


instance
  Setoidᶜᶠ : ISetoid Cfg
  Setoidᶜᶠ ._≈_ c c′ = c ↭ c′

  HNᶜᶠ : BaseCfg has Name
  HNᶜᶠ .collect = λ where
    (⟨ _ ∶ s ♯ _ ⟩)   → [ inj₁ s ]
    (_ ∶ s ♯ _)       → [ inj₁ s ]
    (⟨ _ ,   _ ⟩at x) → [ inj₂ x ]
    (⟨ _ has _ ⟩at x) → [ inj₂ x ]
    _                 → []

  HNᶜᶠ-list : ∀ {X : Set} → ⦃ BaseCfg has X ⦄ → Cfg has X
  HNᶜᶠ-list .collect = concatMap collect


infix -1 _—→_
data _—→_ : Rel₀ Cfg where

  [DEP-AuthJoin] : ∀ {A v x v′ y} {Γ : Cfg} →

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ Γ
        —→
      ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ
