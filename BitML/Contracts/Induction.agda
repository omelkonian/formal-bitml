open import Induction
open import Induction.WellFounded

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

module BitML.Contracts.Induction
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts.Types Participant Honest hiding (C)

data ℂ : Set where
  C   : Contract → ℂ
  CS  : Contracts → ℂ
  VCS : VContracts → ℂ

_∈ℂ_ : Rel ℂ 0ℓ
C c   ∈ℂ CS cs   = c ∈ cs
C c   ∈ℂ VCS vcs = ∃ λ cs → (C c ∈ℂ CS cs) × (CS cs ∈ℂ VCS vcs)
CS cs ∈ℂ VCS vcs = cs ∈ map proj₂ vcs
_     ∈ℂ _       = ⊥

_≺_ : Rel ℂ 0ℓ
CS cs   ≺ C (put _ &reveal _ if _ ⇒ cs′) = cs ≡ cs′
VCS vcs ≺ C (split vcs′)                 = vcs ≡ vcs′
C c     ≺ C (_ ⇒ c′)                     = c ≡ c′
C c     ≺ C (after _ ⇒ c′)               = c ≡ c′
c       ≺ c′                             = c ∈ℂ c′

≺-wf : WellFounded _≺_
≺-wf = acc ∘ flip _≺′_
  where
    _≺′_ : ∀ c′ c → c′ ≺ c → Acc _≺_ c′
    (CS cs   ≺′ C (put _ &reveal _ if _ ⇒ .cs) ) refl = acc (_≺′ CS cs)
    (VCS vcs ≺′ C (split .vcs)  )                refl = acc (_≺′ VCS vcs)
    (C c     ≺′ C (_ ⇒ .c)      )                refl = acc (_≺′ C c)
    (C c     ≺′ C (after _ ⇒ .c))                refl = acc (_≺′ C c)

    (C c ≺′ CS (.c ∷ _)) (here refl) = acc (_≺′ C c)
    (C c ≺′ CS (_ ∷ cs)) (there c∈)  = (C c ≺′ CS cs) c∈

    (C c ≺′ VCS ((v , .cs) ∷ vcs)) (cs , c∈ , here refl) = (C c ≺′ CS cs) c∈
    (C c ≺′ VCS (_ ∷ vcs))         (cs , c∈ , there cs∈) = (C c ≺′ VCS vcs) (cs , c∈ , cs∈)

    (CS cs ≺′ VCS ((v , .cs) ∷ vcs)) (here refl) = acc (_≺′ CS cs)
    (CS cs ≺′ VCS ((v , _)   ∷ vcs)) (there cs∈) = (CS cs ≺′ VCS vcs) cs∈
