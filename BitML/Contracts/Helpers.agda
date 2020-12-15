------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Collections
open import Prelude.Bifunctor

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.Helpers
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest

-- T0D0 use Set'.nub on all results? or only on use-sites

PutComponent = Ids × Secrets × Predicate

private
  variable
    X : Set

names : {{_ : X has Name}} → X → Names
names = collect

namesˡ : {{_ : X has Name}} → X → Secrets
namesˡ = filter₁ ∘ collect {B = Name}

namesʳ : {{_ : X has Name}} → X → Ids
namesʳ = filter₂ ∘ collect {B = Name}

contracts : {{_ : X has Contract}} → X → Contracts
contracts = collect {B = Contract}

secrets : {{_ : X has Secret}} → X → Secrets
secrets = collect {B = Secret}

participants nub-participants : {{_ : X has Participant}} → X → List Participant
participants = collect
nub-participants = nub ∘ participants

putComponents : {{_ : X has PutComponent}} → X → List PutComponent
putComponents = collect

deposits : {{_ : X has DepositRef}} → X → List DepositRef
deposits = collect

instance
  -- Hᵃ : {{_ : Precondition has X}} {{_ : Contracts has X}} → Advertisement has X
  -- Hᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

  Hᵖʳ : {{_ : Arith has X}} → Predicate has X
  Hᵖʳ .collect pr with pr
  ... | `true   = []
  ... | x `∧ y  = collect x ++ collect y
  ... | `¬ x    = collect x
  ... | x `= y  = collect x ++ collect y
  ... | x `< y  = collect x ++ collect y

--

  -- NB: Unfolding recursion inline, in order to convince the termination checker
  HPᶜ : Contract has Participant
  HPᶜ .collect c with c
  -- ... | put _ &reveal _ if _ ⇒ cs = collect cs
  ... | put _ &reveal _ if _ ⇒ []       = []
  ... | put _ &reveal _ if _ ⇒ (c′ ∷ cs) = collect c′ ++ collect (put [] ⇒ cs)
  ... | withdraw p                = [ p ]
  -- ... | split vcs                 = collect vcs
  ... | split []                  = []
  -- ... | split ((_ , cs) ∷ vcs)   = collect (put [] ⇒ cs) ++ collect (split vcs)
  ... | split ((_ , []) ∷ vcs)      = collect (split vcs)
  ... | split ((v , c′ ∷ cs) ∷ vcs) = collect c′ ++ collect (split [ v , cs ]) ++ collect (split vcs)
  ... | p ⇒ c′                    = p ∷ collect c′
  ... | after _ ⇒ c′              = collect c′

  {-# TERMINATING #-}
  HNᶜ : Contract has Name
  HNᶜ .collect c with c
  ... | put xs &reveal as if _ ⇒ cs = map inj₂ xs ++ map inj₁ as ++ collect cs
  ... | withdraw _                = []
  ... | split vcs                 = collect vcs
  ... | _ ⇒ c′                    = collect c′
  ... | after _ ⇒ c′              = collect c′

  HSᶜ : Contract has Secret
  HSᶜ .collect = filter₁ ∘ collect {B = Name}

  {-# TERMINATING #-}
  HPCᶜ : Contract has PutComponent
  HPCᶜ .collect c with c
  ... | put xs &reveal as if p ⇒ cs = (xs , as , p) ∷ collect cs
  ... | withdraw _                  = []
  ... | split vcs                   = collect vcs
  ... | _ ⇒ c′                      = collect c′
  ... | after _ ⇒ c′                = collect c′

--

  HNᵖ : Precondition has Name
  HNᵖ .collect pr with pr
  ... | _ :? _ at x = [ inj₂ x ]
  ... | _ :! _ at x = [ inj₂ x ]
  ... | _ :secret a = [ inj₁ a ]
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HSᵖ : Precondition has Secret
  HSᵖ .collect = filter₁ ∘ collect {B = Name}

  HPᵖ : Precondition has Participant
  HPᵖ .collect pr with pr
  ... | p :? _ at _ = [ p ]
  ... | p :! _ at _ = [ p ]
  ... | p :secret _ = [ p ]
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HDᵖ : Precondition has DepositRef
  HDᵖ .collect pr with pr
  ... | p :? v at x = [ p , v , x ]
  ... | p :! v at x = [ p , v , x ]
  ... | _ :secret _ = []
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

--

  HDᵃ : Advertisement has DepositRef
  HDᵃ .collect = collect ∘ G

  HPᵃ : Advertisement has Participant
  HPᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

  HNᵃ : Advertisement has Name
  HNᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

  HSᵃ : Advertisement has Secret
  HSᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

--

  HSᵃʳ : Arith has Secret
  HSᵃʳ .collect ar with ar
  ... | ` _    = []
  ... | ∣ s ∣  = [ s ]
  ... | x `+ y = collect x ++ collect y
  ... | x `- y = collect x ++ collect y

private
  -- ** check that we get all accessors we want
  ∀C : Set → Set
  ∀C A = (Contract → List A) × (Contracts → List A) × (VContracts → List A)

  ∀P : Set → Set
  ∀P A = (Precondition → List A) × (Advertisement → List A)

  ∀∀ : Set → Set
  ∀∀ A = ∀C A × ∀P A

  _ : ∀∀ Name
  _ = (names , names , names) , (names , names)

  _ : ∀∀ Secret
  _ = (secrets , secrets , secrets) , (secrets , secrets)

  _ : ∀∀ Participant
  _ = (participants , participants , participants) , (participants , participants)

  _ : ∀C PutComponent
  _ = putComponents , putComponents , putComponents

  _ : ∀P DepositRef
  _ = deposits , deposits

secretsOfᵖ : Participant → Precondition → Secrets
secretsOfᵖ A = go
  where
    go : Precondition → Secrets
    go (B :secret s) with A ≟ B
    ... | yes _ = [ s ]
    ... | no  _ = []
    go (l ∣∣ r )     = go l ++ go r
    go _             = []

-- Deposits

persistentDeposits : Precondition → List DepositRef
persistentDeposits (a :! v at x) = [ a , v , x ]
persistentDeposits (p₁ ∣∣ p₂)    = persistentDeposits p₁ ++ persistentDeposits p₂
persistentDeposits _             = []

persistentParticipants : Precondition → List Participant
persistentParticipants (A :! _ at _) = [ A ]
persistentParticipants (l ∣∣ r)      = persistentParticipants l ++ persistentParticipants r
persistentParticipants _             = []

persistent⊆ : persistentParticipants g ⊆ participants g
persistent⊆ {g = A :! _ at _} p∈ = p∈
persistent⊆ {g = l ∣∣ r}      p∈
  with ∈-++⁻ (persistentParticipants l) p∈
... | inj₁ p∈ˡ = ∈-++⁺ˡ (persistent⊆ {g = l} p∈ˡ)
... | inj₂ p∈ʳ = ∈-++⁺ʳ (participants l) (persistent⊆ {g = r} p∈ʳ)

getDeposit : namesʳ g ↦ (Σ[ d ∈ DepositRef ] (proj₁ d ∈ participants g))
getDeposit {g = A :? v at x} (here refl) = (A , v , x) , here refl
getDeposit {g = A :! v at x} (here refl) = (A , v , x) , here refl
getDeposit {g = _ :secret _} ()
getDeposit {g = l ∣∣ r}      x∈
  with _ , y∈ , y≡ ← ∈-mapMaybe⁻ isInj₂ {xs = names l ++ names r} x∈
  with ∈-++⁻ (names l) y∈
... | inj₁ x∈ˡ = map₂′ ∈-++⁺ˡ $ getDeposit {g = l} (∈-mapMaybe⁺ isInj₂ x∈ˡ y≡)
... | inj₂ x∈ʳ = map₂′ (∈-++⁺ʳ (participants l)) $ getDeposit {g = r} (∈-mapMaybe⁺ isInj₂ x∈ʳ y≡)

getName : (A , v , x) ∈ persistentDeposits g
        → x ∈ namesʳ g
getName {g = _ :! _ at _} (here refl) = here refl
getName {g = _ :! _ at _} (there ())
getName {g = l ∣∣ r}      d∈
  with ∈-++⁻ (persistentDeposits l) d∈
... | inj₁ d∈l =
  let _ , y∈ , y≡ = ∈-mapMaybe⁻ isInj₂ {xs = names l} (getName {g = l} d∈l)
  in ∈-mapMaybe⁺ isInj₂ (∈-++⁺ˡ y∈) y≡
... | inj₂ d∈r =
  let _ , y∈ , y≡ = ∈-mapMaybe⁻ isInj₂ {xs = names r} (getName {g = r} d∈r)
  in ∈-mapMaybe⁺ isInj₂ (∈-++⁺ʳ (names l) y∈) y≡

-- Decorations

decorations⊎ : Contract → List (Participant ⊎ Time)
decorations⊎ (A       ⇒ d) = inj₁ A ∷ decorations⊎ d
decorations⊎ (after t ⇒ d) = inj₂ t ∷ decorations⊎ d
decorations⊎ _             = []

decorations : Contract → List Participant × List Time
decorations c = partitionSums (decorations⊎ c)

authDecorations : Contract → List Participant
authDecorations = proj₁ ∘ decorations

timeDecorations : Contract → List Time
timeDecorations = proj₂ ∘ decorations

removeTopDecorations : Contract → Contract
removeTopDecorations (_       ⇒ d) = removeTopDecorations d
removeTopDecorations (after _ ⇒ d) = removeTopDecorations d
removeTopDecorations d             = d

remove-putComponents : (putComponents d) ≡ putComponents (removeTopDecorations d)
remove-putComponents {_       ⇒ d} rewrite remove-putComponents {d} = refl
remove-putComponents {after _ ⇒ d} rewrite remove-putComponents {d} = refl
remove-putComponents {put _ &reveal _ if _ ⇒ _} = refl
remove-putComponents {withdraw _}               = refl
remove-putComponents {split _}                  = refl

remove-names : names d ≡ names (removeTopDecorations d)
remove-names {_       ⇒ d} rewrite remove-names {d} = refl
remove-names {after _ ⇒ d} rewrite remove-names {d} = refl
remove-names {put _ &reveal _ if _ ⇒ _} = refl
remove-names {withdraw _}               = refl
remove-names {split _}                  = refl
