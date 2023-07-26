open import Induction using (Recursor)

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Lists.Collections

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.Induction ⋯ where

open import BitML.Contracts.Types ⋯ hiding (C)

data ℂ : Type where
  D   : Branch     → ℂ
  C   : Contract   → ℂ
  VCS : VContracts → ℂ

data _≺_ : Rel₀ ℂ where

  ≺-∈  : d ∈ ds → D d ≺ C ds
  ≺-∈ᵛ : ds ∈ map proj₂ vcs → C ds ≺ VCS vcs
  instance
    ≺-put   : C ds    ≺ D (put xs &reveal as if p ⇒ ds)
    ≺-auth  : D d     ≺ D (A ∶ d)
    ≺-after : D d     ≺ D (after t ∶ d)
    ≺-split : VCS vcs ≺ D (split vcs)

≺-wf : WellFounded _≺_
≺-wf = acc ∘ _≻_
  where
    _≻_ : ∀ c c′ → c′ ≺ c → Acc _≺_ c′
    (.(C (_ ∷ _))   ≻ .(D _)) (≺-∈                (here refl)) = acc (_ ≻_)
    (.(C (_ ∷ _))   ≻ .(D _)) (≺-∈                (there p))   = (_ ≻ _) (≺-∈ p)
    (.(VCS (_ ∷ _)) ≻ .(C _)) (≺-∈ᵛ {vcs = _ ∷ _} (here refl)) = acc (_ ≻_)
    (.(VCS (_ ∷ _)) ≻ .(C _)) (≺-∈ᵛ {vcs = _ ∷ _} (there p))   = (_ ≻ _) (≺-∈ᵛ p)

    (.(D (put _ &reveal _ if _ ⇒ _)) ≻ .(C _))   ≺-put   = acc (_ ≻_)
    (.(D (_ ∶ _))                    ≻ .(D _))   ≺-auth  = acc (_ ≻_)
    (.(D (after _ ∶ _))              ≻ .(D _))   ≺-after = acc (_ ≻_)
    (.(D (split _))                  ≻ .(VCS _)) ≺-split = acc (_ ≻_)

≺-rec : Recursor (WF.WfRec _≺_)
≺-rec = WF.All.wfRec ≺-wf 0ℓ

record Toℂ (A : Type) : Type where
  field toℂ : A → ℂ
open Toℂ ⦃ ... ⦄ public

_≺ℂ_ : ∀ {A B : Type} ⦃ _ : Toℂ A ⦄ ⦃ _ : Toℂ B ⦄ → A → B → Type
x ≺ℂ y = toℂ x ≺ toℂ y

instance
  Toℂᵈ : Toℂ Branch
  Toℂᵈ .toℂ = D

  Toℂᶜ : Toℂ Contract
  Toℂᶜ .toℂ = C

  Toℂᵛᶜˢ : Toℂ VContracts
  Toℂᵛᶜˢ .toℂ = VCS

  -- HP-ℂ : ∀ {X : Type} ⦃ _ : Branch has X ⦄ → ℂ has X
  -- HP-ℂ .collect (D d)     = collect d
  -- HP-ℂ .collect (C ds)    = collect ds
  -- HP-ℂ .collect (VCS vcs) = collect vcs
