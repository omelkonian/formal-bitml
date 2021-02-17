open import Induction using (Recursor)

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Collections

module BitML.Contracts.Induction
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Predicate
open import BitML.Contracts.Types Participant Honest
  hiding (C)

data ℂ : Set where
  C   : Contract → ℂ
  CS  : Contracts → ℂ
  VCS : VContracts → ℂ

data _≺_ : Rel ℂ 0ℓ where

  ≺-∈  : d ∈ ds → C d ≺ CS ds
  ≺-∈ᵛ : ds ∈ map proj₂ vcs → CS ds ≺ VCS vcs
  instance
    ≺-put   : CS ds ≺ C (put xs &reveal as if p ⇒ ds)
    ≺-auth  : C d ≺ C (A ⇒ d)
    ≺-after : C d ≺ C (after t ⇒ d)
    ≺-split : VCS vcs ≺ C (split vcs)

≺-wf : WellFounded _≺_
≺-wf = acc ∘ _≻_
  where
    _≻_ : ∀ c c′ → c′ ≺ c → Acc _≺_ c′
    (.(CS (_ ∷ _))  ≻ .(C _))  (≺-∈                (here refl)) = acc (_ ≻_)
    (.(CS (_ ∷ _))  ≻ .(C _))  (≺-∈                (there p))   = (_ ≻ _) (≺-∈ p)
    (.(VCS (_ ∷ _)) ≻ .(CS _)) (≺-∈ᵛ {vcs = _ ∷ _} (here refl)) = acc (_ ≻_)
    (.(VCS (_ ∷ _)) ≻ .(CS _)) (≺-∈ᵛ {vcs = _ ∷ _} (there p))   = (_ ≻ _) (≺-∈ᵛ p)

    (.(C (put _ &reveal _ if _ ⇒ _)) ≻ .(CS _))  ≺-put   = acc (_ ≻_)
    (.(C (_ ⇒ _))                    ≻ .(C _))   ≺-auth  = acc (_ ≻_)
    (.(C (after _ ⇒ _))              ≻ .(C _))   ≺-after = acc (_ ≻_)
    (.(C (split _))                  ≻ .(VCS _)) ≺-split = acc (_ ≻_)

≺-rec : Recursor (WF.WfRec _≺_)
≺-rec = WF.All.wfRec ≺-wf 0ℓ

record Toℂ (A : Set) : Set where
  field toℂ : A → ℂ
open Toℂ {{...}} public

_≺ℂ_ : ∀ {A B : Set} {{_ : Toℂ A}} {{_ : Toℂ B}} → A → B → Set
x ≺ℂ y = toℂ x ≺ toℂ y

instance
  Toℂᶜ : Toℂ Contract
  Toℂᶜ .toℂ = C

  Toℂᶜˢ : Toℂ Contracts
  Toℂᶜˢ .toℂ = CS

  Toℂᵛᶜˢ : Toℂ VContracts
  Toℂᵛᶜˢ .toℂ = VCS

  -- HP-ℂ : ∀ {X : Set} {{_ : Contract has X}} → ℂ has X
  -- HP-ℂ .collect (C d)     = collect d
  -- HP-ℂ .collect (CS ds)   = collect ds
  -- HP-ℂ .collect (VCS vcs) = collect vcs
