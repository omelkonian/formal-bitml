------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------
{-# OPTIONS --postfix-projections #-}

open import Function using (_∘_)

open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Nat     using (_>_)

open import Data.List using (List; []; _∷_; [_]; length; _++_; map; concatMap; partitionSums)
open import Data.List.NonEmpty using (List⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists
open import Prelude.DecEq

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
    X Y Z : Set

record _has_ (A : Set) (B : Set) : Set where
  field
    collect : A → List B
open _has_ {{...}} public

instance
  -- H-refl : X has X
  -- H-refl .collect = [_]

  -- {-# TERMINATING #-}
  H-List : ∀ {{_ : X has Y}} → List X has Y
  H-List .collect = concatMap collect
  -- H-List .collect []       = []
  -- H-List .collect (x ∷ xs) = collect x ++ collect xs

  -- H-×ˡ : ∀ {{_ : X has Z}} → (X × Y) has Z
  -- H-×ˡ .collect (x , _) = collect x

  H-×ʳ : ∀ {{_ : Y has Z}} → (X × Y) has Z
  H-×ʳ .collect (_ , y) = collect y

  -- H-⊎ : {{_ : X has Z}} {{_ : Y has Z} → (X ⊎ Y) has Z
  -- H-⊎ .collect (inj₁ x) = collect x
  -- H-⊎ .collect (inj₂ y) = collect y

  -- H-⊎ˡ : {{_ : X has Z}} → (X ⊎ Y) has Z
  -- H-⊎ˡ .collect (inj₁ x) = collect x
  -- H-⊎ˡ .collect (inj₂ _) = []

  -- H-⊎ʳ : {{_ : Y has Z}} → (X ⊎ Y) has Z
  -- H-⊎ʳ .collect (inj₁ _) = []
  -- H-⊎ʳ .collect (inj₂ y) = collect y

  -- H-⊎ˡ : {{_ : X has (Y ⊎ Z)}} → X has Y
  -- H-⊎ˡ {Y = Y}{Z} {{h}} .collect  = filter₁ {A = Y}{B = Z} ∘ collect {{h}}

  -- H-⊎ʳ : {{_ : X has (Y ⊎ Z)}} → X has Z
  -- H-⊎ʳ {Y = Y}{Z} {{h}} .collect  = filter₂ {A = Y}{B = Z} ∘ collect {{h}}

  -- H-List : List X has X
  -- H-List .collect x = x

  -- H-×ʳ : (X × Y) has Y
  -- H-×ʳ .collect (_ , x) = [ x ]

  -- H-trans : {{_ : X has Y}} {{_ : Y has Z}} → X has Z
  -- H-trans {{p}} {{q}} .collect = concatMap (collect {{q}}) ∘ collect {{p}}

names : {{_ : X has Name}} → X → Names
names = collect

contracts : {{_ : X has Contract}} → X → Contracts
contracts = collect {B = Contract}

secrets : {{_ : X has Secret}} → X → Secrets
secrets = collect {B = Secret}

participants : {{_ : X has Participant}} → X → List Participant
participants = collect

putComponents : {{_ : X has PutComponent}} → X → List PutComponent
putComponents = collect

deposits : {{_ : X has DepositRef}} → X → List DepositRef
deposits = collect

instance
  Hᵃ : {{_ : Precondition has X}} → Advertisement has X
  Hᵃ .collect (⟨ G ⟩ _) = collect G

  Hᵖʳ : {{_ : Arith has X}} → Predicate has X
  Hᵖʳ .collect pr with pr
  ... | `true   = []
  ... | x `∧ y  = collect x ++ collect y
  ... | `¬ x    = collect x
  ... | x `= y  = collect x ++ collect y
  ... | x `< y  = collect x ++ collect y

--
  -- HCᵛᶜˢ : VContracts has Contract
  -- HCᵛᶜˢ .collect = concatMap proj₂

  -- Hᶜˢ : {{_ : Contract has X}} → Contracts has X
  -- Hᶜˢ .collect = concatMap collect

  -- Hᵛᶜˢ : {{_ : Contract has X}} → VContracts has X
  -- Hᵛᶜˢ .collect = concatMap (collect ∘ proj₂)

--

  -- NB: Unfolding recursion inline, in order to convice the termination checker
  HPᶜ : Contract has Participant
  HPᶜ .collect c with c
  -- ... | put _ &reveal _ if _ ⇒ cs = collect cs
  ... | put _ &reveal _ if _ ⇒ []       = []
  ... | put _ &reveal _ if _ ⇒ (c′ ∷ cs) = collect c′ ++ collect (put [] ⇒ cs)
  ... | withdraw p                = [ p ]
  -- ... | split vcs                 = collect vcs
  ... | split []                  = []
  -- ... | split ((_ , c′) ∷ vcs)   = collect c′ ++ collect (split vcs)
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

  -- HIᶜ : Contract has Id
  -- HIᶜ .collect = filter₂ ∘ collect {B = Name}

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

  -- HIᵖ : Precondition has Id
  -- HIᵖ .collect = filter₂ ∘ collect {B = Name}

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

  HSᵃʳ : Arith has Secret
  HSᵃʳ .collect ar with ar
  ... | ` _    = []
  ... | ∣ s ∣  = [ s ]
  ... | x `+ y = collect x ++ collect y
  ... | x `- y = collect x ++ collect y

--

  -- HC⇒HPC : {{_ : X has Contract}} → X has PutComponent
  -- HC⇒HPC .collect = concatMap (putComponents {{HPCᶜ}}) ∘ collect {B = Contract}

  -- HC⇒HN : {{_ : X has Contract}} → X has Name
  -- HC⇒HN .collect = concatMap (names {{HNᶜ}}) ∘ collect {B = Contract}


--

private
  -- _ : List (X × Y) → List Y
  -- _ = collect

  -- _ : {{_ : X has Contract}} → X → List PutComponent
  -- _ = putComponents

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
persistentDeposits = go
  where
    go : Precondition → List DepositRef
    go (a :! v at x) = [ a , v , x ]
    go (p₁ ∣∣ p₂)    = go p₁ ++ go p₂
    go _             = []

persistentParticipants : Precondition → List Participant
persistentParticipants = go
  where
    go : Precondition → List Participant
    go (A :! _ at _) = [ A ]
    go (p ∣∣ p₁)     = go p ++ go p₁
    go _             = []

getDeposit : ∀ {x} {g : Precondition} → inj₂ x ∈ names g → DepositRef
getDeposit {g = A :? v at x} (here refl) = A , v , x
getDeposit {g = A :! v at x} (here refl) = A , v , x
getDeposit {g = _ :secret _} (here ())
getDeposit {g = _ :secret _} (there ())
getDeposit {g = l ∣∣ r}      x∈
  with ∈-++⁻ (names l) x∈
... | inj₁ x∈l = getDeposit {g = l} x∈l
... | inj₂ x∈r = getDeposit {g = r} x∈r

getName : (A , v , x) ∈ persistentDeposits g
        → inj₂ x ∈ names g
getName {g = _ :! _ at _} (here refl) = here refl
getName {g = _ :! _ at _} (there ())
getName {g = l ∣∣ r}      d∈
  with ∈-++⁻ (persistentDeposits l) d∈
... | inj₁ d∈l = ∈-++⁺ˡ (getName {g = l} d∈l)
... | inj₂ d∈r = ∈-++⁺ʳ _ (getName {g = r} d∈r)

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
