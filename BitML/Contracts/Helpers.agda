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
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types     Participant Honest
  hiding (C)
open import BitML.Contracts.Induction Participant Honest

-- T0D0 use Set'.nub on all results? or only on use-sites

PutComponent = Ids × Secrets × Predicate

private
  variable
    X : Set

----------------
-- ** Collectors

mkCollect : (∀ e → (∀ e′ → e′ ≺ C e → List X) → List X) → ℂ → List X
mkCollect {X = X} mk = ≺-rec _ go
  where
    go : ∀ c → (∀ c′ → c′ ≺ c → List X) → List X
    go (C c)     f = mk c f
    go (CS cs)   f = concat $ mapWith∈ cs (f (C _) ∘ ≺-∈)
    go (VCS vcs) f = concat $ mapWith∈ (map proj₂ vcs) (f (CS _) ∘ ≺-∈ᵛ)

instance
  -- Hℂ : ⦃ _ : Contract has X ⦄ → ℂ has X
  -- Hℂ .collect = mkCollect (λ e _ → collect e)

  Hℂ : ⦃ _ : Contract has X ⦄ ⦃ _ : Contracts has X ⦄ ⦃ _ : VContracts has X ⦄ → ℂ has X
  Hℂ .collect 𝕔 with 𝕔
  ... | C c = collect c
  ... | CS cs = collect cs
  ... | VCS vcs = collect vcs

-- participants

participantsℂ : ℂ → List Participant
participantsℂ = mkCollect go
  where
    go : ∀ e → (∀ e′ → e′ ≺ C e → List Participant) → List Participant
    go c f with c
    ... | put _ &reveal _ if _ ⇒ cs = f (CS cs) it
    ... | withdraw p                = [ p ]
    ... | split vcs                 = f (VCS vcs) it
    ... | p ⇒ c′                    = p ∷ f (C c′) it
    ... | after _ ⇒ c′              = f (C c′) it

instance
  HPᶜ : Contract has Participant
  HPᶜ .collect = participantsℂ ∘ C

  HPᶜˢ : Contracts has Participant
  HPᶜˢ .collect = participantsℂ ∘ CS

  HPᵛᶜˢ : VContracts has Participant
  HPᵛᶜˢ .collect = participantsℂ ∘ VCS

  HPᵖ : Precondition has Participant
  HPᵖ .collect pr with pr
  ... | p :? _ at _ = [ p ]
  ... | p :! _ at _ = [ p ]
  ... | p :secret _ = [ p ]
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HPᵃ : Advertisement has Participant
  HPᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

participants nub-participants : ⦃ _ :  X has Participant ⦄ → X → List Participant
participants = collect
nub-participants = nub ∘ participants

-- names

namesℂ : ℂ → List Name
namesℂ = mkCollect go
  where
    go : ∀ e → (∀ e′ → e′ ≺ C e → List Name) → List Name
    go c f with c
    ... | put xs &reveal as if _ ⇒ cs = map inj₂ xs ++ map inj₁ as ++ f (CS cs) it
    ... | withdraw _                  = []
    ... | split vcs                   = f (VCS vcs) it
    ... | _ ⇒ c′                      = f (C c′) it
    ... | after _ ⇒ c′                = f (C c′) it

instance
  HNᶜ : Contract has Name
  HNᶜ .collect = namesℂ ∘ C

  HNᶜˢ : Contracts has Name
  HNᶜˢ .collect = namesℂ ∘ CS

  HNᵛᶜˢ : VContracts has Name
  HNᵛᶜˢ .collect = namesℂ ∘ VCS

  HNᵖ : Precondition has Name
  HNᵖ .collect pr with pr
  ... | _ :? _ at x = [ inj₂ x ]
  ... | _ :! _ at x = [ inj₂ x ]
  ... | _ :secret a = [ inj₁ a ]
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HNᵃ : Advertisement has Name
  HNᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

names : ⦃ _ :  X has Name ⦄ → X → Names
names = collect

namesˡ : ⦃ _ :  X has Name ⦄ → X → Secrets
namesˡ = filter₁ ∘ names

namesʳ : ⦃ _ :  X has Name ⦄ → X → Ids
namesʳ = filter₂ ∘ names

-- secrets
-- T0D0: reuse `names` generically

instance

  HSᵃʳ : Arith has Secret
  HSᵃʳ .collect ar with ar
  ... | ` _    = []
  ... | ∣ s ∣  = [ s ]
  ... | x `+ y = collect x ++ collect y
  ... | x `- y = collect x ++ collect y

  Hᵖʳ : ⦃ _ :  Arith has X ⦄ → Predicate has X
  Hᵖʳ .collect pr with pr
  ... | `true   = []
  ... | x `∧ y  = collect x ++ collect y
  ... | `¬ x    = collect x
  ... | x `= y  = collect x ++ collect y
  ... | x `< y  = collect x ++ collect y

  -- HN→HS : ⦃ _ : X has Name ⦄ → X has Secret
  -- HN→HS .collect = filter₁ ∘ collect {B = Name}

  HSᶜ : Contract has Secret
  HSᶜ .collect = filter₁ ∘ collect {B = Name}

  HSᶜˢ : Contracts has Secret
  HSᶜˢ .collect = filter₁ ∘ collect {B = Name}

  HSᵛᶜˢ : VContracts has Secret
  HSᵛᶜˢ .collect = filter₁ ∘ collect {B = Name}

  HSᵖ : Precondition has Secret
  HSᵖ .collect = filter₁ ∘ collect {B = Name}

  HSᵃ : Advertisement has Secret
  HSᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c

secrets : ⦃ _ :  X has Secret ⦄ → X → Secrets
secrets = collect

-- put components

putComponentsℂ : ℂ → List PutComponent
putComponentsℂ = mkCollect go
  where
    go : ∀ c → (∀ c′ → c′ ≺ C c → List PutComponent) → List PutComponent
    go c f with c
    ... | put xs &reveal as if p ⇒ cs = (xs , as , p) ∷ f (CS cs) it
    ... | withdraw _                  = []
    ... | split vcs                   = f (VCS vcs) it
    ... | _ ⇒ c′                      = f (C c′) it
    ... | after _ ⇒ c′                = f (C c′) it

instance
  HPCᶜ : Contract has PutComponent
  HPCᶜ .collect = putComponentsℂ ∘ C

  HPCᶜˢ : Contracts has PutComponent
  HPCᶜˢ .collect = putComponentsℂ ∘ CS

  HPCᵛᶜˢ : VContracts has PutComponent
  HPCᵛᶜˢ .collect = putComponentsℂ ∘ VCS

putComponents : ⦃ _ :  X has PutComponent ⦄ → X → List PutComponent
putComponents = collect

-- deposits

instance
  HDᵖ : Precondition has DepositRef
  HDᵖ .collect pr with pr
  ... | p :? v at x = [ p , v , x ]
  ... | p :! v at x = [ p , v , x ]
  ... | _ :secret _ = []
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HDᵃ : Advertisement has DepositRef
  HDᵃ .collect = collect ∘ G

deposits : ⦃ _ :  X has DepositRef ⦄ → X → List DepositRef
deposits = collect

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

-- Subterms

subterms subterms⁺ subterms′ : ℂ → Contracts

subterms c@(C _)   = drop 1 $ subterms⁺ c
subterms c@(CS _)  = subterms⁺ c
subterms c@(VCS _) = subterms⁺ c

subterms⁺ = mkCollect go
  where
    go : ∀ c → (∀ c′ → c′ ≺ C c → Contracts) → Contracts
    go c f with c
    ... | _ ⇒ d                      = f (C d) it
    ... | after _ ⇒ d                = f (C d) it
    ... | split vcs                  = c ∷ f (VCS vcs) it
    ... | put _ &reveal _ if _ ⇒ cs  = c ∷ f (CS cs) it
    ... | withdraw _                 = c ∷ []

subterms′ (C c) with c
... | _ ⇒ d                      = subterms′ (C d)
... | after _ ⇒ d                = subterms′ (C d)
... | split vcs                  = subterms′ (VCS vcs)
... | put _ &reveal _ if _ ⇒ cs  = subterms′ (CS cs)
... | withdraw _                 = []
subterms′ (CS [])                = []
subterms′ (CS (c ∷ cs))          = c ∷ subterms′ (C c) ++ subterms′ (CS cs)
subterms′ (VCS [])               = []
subterms′ (VCS ((_ , cs) ∷ vcs)) = subterms′ (CS cs) ++ subterms′ (VCS vcs)

-- Lemmas about `subterms`

↦-∈ : ∀ {R : Set}
  → (∀ {d} → d ∈ ds → subterms⁺ (C d) ↦ R)
  → subterms⁺ (CS ds) ↦ R
↦-∈ {ds = c ∷ cs} f x∈
  with ∈-++⁻ (subterms⁺ (C c)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ (f ∘ there) x∈ʳ

↦-∈ᵛ : ∀ {R : Set}
  → (∀ {cs} → cs ∈ map proj₂ vcs → subterms⁺ (CS cs) ↦ R)
  → subterms⁺ (VCS vcs) ↦ R
↦-∈ᵛ {vcs = (_ , cs) ∷ vcs} f x∈
  with ∈-++⁻ (subterms⁺ (CS cs)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ᵛ (f ∘ there) x∈ʳ

subterms⊆ᶜˢ : ds ⊆ subterms′ (CS ds)
subterms⊆ᶜˢ {ds = d ∷ ds} (here refl) = here refl
subterms⊆ᶜˢ {ds = d ∷ ds} (there d∈)  = there $ ∈-++⁺ʳ (subterms′ $ C d) (subterms⊆ᶜˢ d∈)

subterms⊆ᵛᶜˢ : (v , ds) ∈ vcs → ds ⊆ subterms′ (VCS vcs)
subterms⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} (here refl) = ∈-++⁺ˡ ∘ subterms⊆ᶜˢ
subterms⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} (there p)   = ∈-++⁺ʳ (subterms′ (CS ds)) ∘ subterms⊆ᵛᶜˢ p

subterms′-names⊆ᶜ : d ∈ subterms′ (C d′) → names d ⊆ names d′
subterms′-names⊆ᶜˢ : d ∈ subterms′ (CS ds) → names d ⊆ names ds
subterms′-names⊆ᵛᶜˢ : d ∈ subterms′ (VCS vcs) → names d ⊆ names vcs

subterms′-names⊆ᶜ {d′ = put xs &reveal as if _ ⇒ ds} x∈ =
  ∈-++⁺ʳ (map inj₂ xs) ∘ ∈-++⁺ʳ (map inj₁ as) ∘ subterms′-names⊆ᶜˢ {ds = ds} x∈
subterms′-names⊆ᶜ {d′ = withdraw _} ()
subterms′-names⊆ᶜ {d′ = split vcs}    = subterms′-names⊆ᵛᶜˢ {vcs = vcs}
subterms′-names⊆ᶜ {d′ = _ ⇒ d′}       = subterms′-names⊆ᶜ {d′ = d′}
subterms′-names⊆ᶜ {d′ = after _ ⇒ d′} = subterms′-names⊆ᶜ {d′ = d′}

subterms′-names⊆ᶜˢ {ds = d ∷ ds} (here refl) = ∈-++⁺ˡ
subterms′-names⊆ᶜˢ {ds = d ∷ ds} (there p)
  with ∈-++⁻ _ p
... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᶜˢ {ds = ds} p′
... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-names⊆ᶜ {d′ = d} p′

subterms′-names⊆ᵛᶜˢ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᵛᶜˢ {vcs = vcs} p
subterms′-names⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} p
  with ∈-++⁻ (subterms′ (CS ds)) p
... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-names⊆ᶜˢ {ds = ds} p′
... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᵛᶜˢ {vcs = vcs} p′

subterms′-putComponents⊆ᶜ : d ∈ subterms′ (C d′) → putComponents d ⊆ putComponents d′
subterms′-putComponents⊆ᶜˢ : d ∈ subterms′ (CS ds) → putComponents d ⊆ putComponents ds
subterms′-putComponents⊆ᵛᶜˢ : d ∈ subterms′ (VCS vcs) → putComponents d ⊆ putComponents vcs

subterms′-putComponents⊆ᶜ {d′ = put xs &reveal as if _ ⇒ ds} x∈ = there ∘ subterms′-putComponents⊆ᶜˢ {ds = ds} x∈
subterms′-putComponents⊆ᶜ {d′ = withdraw _} ()
subterms′-putComponents⊆ᶜ {d′ = split vcs}    = subterms′-putComponents⊆ᵛᶜˢ {vcs = vcs}
subterms′-putComponents⊆ᶜ {d′ = _ ⇒ d′}       = subterms′-putComponents⊆ᶜ {d′ = d′}
subterms′-putComponents⊆ᶜ {d′ = after _ ⇒ d′} = subterms′-putComponents⊆ᶜ {d′ = d′}

subterms′-putComponents⊆ᶜˢ {ds = d ∷ ds} (here refl) = ∈-++⁺ˡ
subterms′-putComponents⊆ᶜˢ {ds = d ∷ ds} (there p)
  with ∈-++⁻ _ p
... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᶜˢ {ds = ds} p′
... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-putComponents⊆ᶜ {d′ = d} p′

subterms′-putComponents⊆ᵛᶜˢ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᵛᶜˢ {vcs = vcs} p
subterms′-putComponents⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} p
  with ∈-++⁻ (subterms′ (CS ds)) p
... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-putComponents⊆ᶜˢ {ds = ds} p′
... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᵛᶜˢ {vcs = vcs} p′
