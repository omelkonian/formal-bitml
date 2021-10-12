------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Collections
open import Prelude.Bifunctor
open import Prelude.General

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

private variable X : Set

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
    ... | put _ &reveal _ if _ ⇒ cs = f (CS cs) ≺-put -- it
    ... | withdraw p                = [ p ]
    ... | split vcs                 = f (VCS vcs) ≺-split -- it
    ... | p ⇒ c′                    = p ∷ f (C c′) ≺-auth -- it
    ... | after _ ⇒ c′              = f (C c′) ≺-after -- it

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
  -- HPᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c
  HPᵃ .collect = collect ∘ G

participants nub-participants : ⦃ _ :  X has Participant ⦄ → X → List Participant
participants = collect
nub-participants = nub ∘ participants

-- names

namesℂ : ℂ → List Name
namesℂ = mkCollect go
  where
    go : ∀ e → (∀ e′ → e′ ≺ C e → List Name) → List Name
    go c f with c
    ... | put xs &reveal as if _ ⇒ cs = map inj₂ xs ++ map inj₁ as ++ f (CS cs) ≺-put -- it
    ... | withdraw _                  = []
    ... | split vcs                   = f (VCS vcs) ≺-split -- it
    ... | _ ⇒ c′                      = f (C c′) ≺-auth -- it
    ... | after _ ⇒ c′                = f (C c′) ≺-after -- it

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
  -- HNᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c
  HNᵃ .collect = collect ∘ G

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
  -- HSᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c
  HSᵃ .collect = collect ∘ G

secrets : ⦃ _ :  X has Secret ⦄ → X → Secrets
secrets = collect

-- put components

putComponentsℂ : ℂ → List PutComponent
putComponentsℂ = mkCollect go
  where
    go : ∀ c → (∀ c′ → c′ ≺ C c → List PutComponent) → List PutComponent
    go c f with c
    ... | put xs &reveal as if p ⇒ cs = (xs , as , p) ∷ f (CS cs) ≺-put -- it
    ... | withdraw _                  = []
    ... | split vcs                   = f (VCS vcs) ≺-split -- it
    ... | _ ⇒ c′                      = f (C c′) ≺-auth -- it
    ... | after _ ⇒ c′                = f (C c′) ≺-after -- it

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
  -- HD⇒HD : ⦃ _ : X has TDepositRef ⦄ → X has DepositRef
  -- HD⇒HD ⦃ hd ⦄ .collect = map proj₂ ∘ collect ⦃ hd ⦄

  HTDᵖ : Precondition has TDepositRef
  HTDᵖ .collect pr with pr
  ... | p :? v at x = [ volatile   , p , v , x ]
  ... | p :! v at x = [ persistent , p , v , x ]
  ... | _ :secret _ = []
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HDᵖ : Precondition has DepositRef
  HDᵖ .collect = map proj₂ ∘ collect

  HTDᵃ : Advertisement has TDepositRef
  HTDᵃ .collect = collect ∘ G

  HDᵃ : Advertisement has DepositRef
  HDᵃ .collect = map proj₂ ∘ collect

tdeposits : ⦃ _ :  X has TDepositRef ⦄ → X → List TDepositRef
tdeposits = collect

deposits : ⦃ _ :  X has DepositRef ⦄ → X → List DepositRef
deposits ⦃ hd ⦄ = collect ⦃ hd ⦄

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

  _ : ∀P TDepositRef
  _ = tdeposits , tdeposits

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

namesˡ⇒part : a ∈ namesˡ g → Σ Participant (_∈ nub-participants g)
namesˡ⇒part {a}{A :secret .a} (here refl) = -, here refl
namesˡ⇒part {a}{l ∣∣ r} a∈
  rewrite mapMaybe-++ isInj₁ (names l) (names r)
  with L.Mem.∈-++⁻ (namesˡ l) a∈
... | inj₁ a∈ˡ = map₂′ (∈-nub⁺ ∘ L.Mem.∈-++⁺ˡ {xs = participants l} ∘ ∈-nub⁻) $ namesˡ⇒part {g = l} a∈ˡ
... | inj₂ a∈ʳ = map₂′ (∈-nub⁺ ∘ L.Mem.∈-++⁺ʳ (participants l) ∘ ∈-nub⁻) $ namesˡ⇒part {g = r} a∈ʳ

names⊆secretsOf : (a∈ : a ∈ namesˡ g) → a ∈ secretsOfᵖ (proj₁ $ namesˡ⇒part {g = g} a∈) g
names⊆secretsOf {a}{g = A :secret .a} (here refl) rewrite ≟-refl _≟_ A = here refl
names⊆secretsOf {a}{g = l ∣∣ r} a∈
  rewrite mapMaybe-++ isInj₁ (names l) (names r)
  with L.Mem.∈-++⁻ (namesˡ l) a∈
... | inj₁ a∈ˡ = L.Mem.∈-++⁺ˡ (names⊆secretsOf {g = l} a∈ˡ)
... | inj₂ a∈ʳ = L.Mem.∈-++⁺ʳ _ (names⊆secretsOf {g = r} a∈ʳ)

-- Deposits

isVolatile isPersistent : TDepositRef → Maybe DepositRef
isVolatile = case_of λ where
  (volatile   , d) → just d
  (persistent , _) → nothing
isPersistent = case_of λ where
  (volatile   , _) → nothing
  (persistent , d) → just d

volatileDeposits persistentDeposits : Precondition → List DepositRef
volatileDeposits   = mapMaybe isVolatile   ∘ tdeposits
persistentDeposits = mapMaybe isPersistent ∘ tdeposits

persistentValue : Precondition → Value
persistentValue = ∑ℕ ∘ map (proj₁ ∘ proj₂) ∘ persistentDeposits

volatileParticipants persistentParticipants : Precondition → List Participant
volatileParticipants   = map proj₁ ∘ volatileDeposits
persistentParticipants = map proj₁ ∘ persistentDeposits

volatileNamesʳ persistentNamesʳ : Precondition → Ids
volatileNamesʳ   = map (proj₂ ∘ proj₂) ∘ volatileDeposits
persistentNamesʳ = map (proj₂ ∘ proj₂) ∘ persistentDeposits

volatileNames⊆ : volatileNamesʳ g ⊆ namesʳ g
volatileNames⊆ {g = A :? v at x} n∈ = n∈
volatileNames⊆ {g = l ∣∣ r}  {n} n∈
  with (p , v , .n) , d∈ , refl ← ∈-map⁻ (proj₂ ∘ proj₂) n∈
  with _ , d∈ , d≡ ← ∈-mapMaybe⁻ isVolatile {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-++⁻ (tdeposits l) d∈
... | inj₁ d∈ˡ
  with (_ , m∈ , m≡) ← ∈-mapMaybe⁻ isInj₂ {xs = names l} $ volatileNames⊆ {g = l}
                     $ ∈-map⁺ (proj₂ ∘ proj₂)
                     $ ∈-mapMaybe⁺ isVolatile d∈ˡ d≡
  = ∈-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-++⁺ˡ m∈) m≡
... | inj₂ d∈ʳ
  with (_ , m∈ , m≡) ← ∈-mapMaybe⁻ isInj₂ {xs = names r} $ volatileNames⊆ {g = r}
                     $ ∈-map⁺ (proj₂ ∘ proj₂)
                     $ ∈-mapMaybe⁺ isVolatile d∈ʳ d≡
  = ∈-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-++⁺ʳ (names l) m∈) m≡

persistentNames⊆ : persistentNamesʳ g ⊆ namesʳ g
persistentNames⊆ {g = A :! v at x} n∈ = n∈
persistentNames⊆ {g = l ∣∣ r}  {n} n∈
  with (p , v , .n) , d∈ , refl ← ∈-map⁻ (proj₂ ∘ proj₂) n∈
  with _ , d∈ , d≡ ← ∈-mapMaybe⁻ isPersistent {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-++⁻ (tdeposits l) d∈
... | inj₁ d∈ˡ
  with (_ , m∈ , m≡) ← ∈-mapMaybe⁻ isInj₂ {xs = names l} $ persistentNames⊆ {g = l}
                     $ ∈-map⁺ (proj₂ ∘ proj₂)
                     $ ∈-mapMaybe⁺ isPersistent d∈ˡ d≡
  = ∈-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-++⁺ˡ m∈) m≡
... | inj₂ d∈ʳ
  with (_ , m∈ , m≡) ← ∈-mapMaybe⁻ isInj₂ {xs = names r} $ persistentNames⊆ {g = r}
                     $ ∈-map⁺ (proj₂ ∘ proj₂)
                     $ ∈-mapMaybe⁺ isPersistent d∈ʳ d≡
  = ∈-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-++⁺ʳ (names l) m∈) m≡

volatileParticipants⊆ : volatileParticipants g ⊆ participants g
volatileParticipants⊆ {g = A :? _ at _} p∈ = p∈
volatileParticipants⊆ {g = l ∣∣ r} {p} p∈
  with (.p , v , x) , d∈ , refl ← ∈-map⁻ proj₁ p∈
  with _ , d∈ , d≡ ← ∈-mapMaybe⁻ isVolatile {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-++⁻ (tdeposits l) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ (volatileParticipants⊆ {g = l} $ ∈-map⁺ proj₁ $ ∈-mapMaybe⁺ isVolatile d∈ˡ d≡)
... | inj₂ d∈ʳ = ∈-++⁺ʳ (participants l) (volatileParticipants⊆ {g = r} $ ∈-map⁺ proj₁ $ ∈-mapMaybe⁺ isVolatile d∈ʳ d≡)

persistentParticipants⊆ : persistentParticipants g ⊆ participants g
persistentParticipants⊆ {g = A :! _ at _} p∈ = p∈
persistentParticipants⊆ {g = l ∣∣ r} {p} p∈
  with (.p , v , x) , d∈ , refl ← ∈-map⁻ proj₁ p∈
  with _ , d∈ , d≡ ← ∈-mapMaybe⁻ isPersistent {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-++⁻ (tdeposits l) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ (persistentParticipants⊆ {g = l} $ ∈-map⁺ proj₁ $ ∈-mapMaybe⁺ isPersistent d∈ˡ d≡)
... | inj₂ d∈ʳ = ∈-++⁺ʳ (participants l) (persistentParticipants⊆ {g = r} $ ∈-map⁺ proj₁ $ ∈-mapMaybe⁺ isPersistent d∈ʳ d≡)

getDeposit : namesʳ g ↦ (Σ[ d ∈ DepositRef ] (proj₁ d ∈ participants g))
getDeposit {g = A :? v at x} (here refl) = (A , v , x) , here refl
getDeposit {g = A :! v at x} (here refl) = (A , v , x) , here refl
getDeposit {g = _ :secret _} ()
getDeposit {g = l ∣∣ r}      x∈
  with _ , y∈ , y≡ ← ∈-mapMaybe⁻ isInj₂ {xs = names l ++ names r} x∈
  with ∈-++⁻ (names l) y∈
... | inj₁ x∈ˡ = map₂′ ∈-++⁺ˡ $ getDeposit {g = l} (∈-mapMaybe⁺ isInj₂ x∈ˡ y≡)
... | inj₂ x∈ʳ = map₂′ (∈-++⁺ʳ (participants l)) $ getDeposit {g = r} (∈-mapMaybe⁺ isInj₂ x∈ʳ y≡)

checkDeposit : DepositType → Id → Precondition → Maybe Value
checkDeposit ty x
  = L.head ∘ map (proj₁ ∘ proj₂) ∘ filter ((_≟ x) ∘ proj₂ ∘ proj₂)
  ∘ (case ty of λ{ persistent → persistentDeposits; volatile → volatileDeposits })

getName : (A , v , x) ∈ persistentDeposits g
        → x ∈ namesʳ g
getName {g = _ :! _ at _} (here refl) = here refl
getName {g = _ :! _ at _} (there ())
getName {g = l ∣∣ r}      d∈
  with _ , td∈ , td≡ ← ∈-mapMaybe⁻ isPersistent {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-++⁻ (tdeposits l) td∈
... | inj₁ d∈ˡ =
  let _ , y∈ , y≡ = ∈-mapMaybe⁻ isInj₂ {xs = names l} (getName {g = l} $ ∈-mapMaybe⁺ isPersistent d∈ˡ td≡)
  in ∈-mapMaybe⁺ isInj₂ (∈-++⁺ˡ y∈) y≡
... | inj₂ d∈ʳ =
  let _ , y∈ , y≡ = ∈-mapMaybe⁻ isInj₂ {xs = names r} (getName {g = r} $ ∈-mapMaybe⁺ isPersistent d∈ʳ td≡)
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

infix 0 _≡⋯∶_
_≡⋯∶_ : Rel₀ Contract
d ≡⋯∶ d′ = removeTopDecorations d ≡ d′

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
    ... | _       ⇒ d                = f (C d) ≺-auth -- it
    ... | after _ ⇒ d                = f (C d) ≺-after -- it
    ... | split vcs                  = c ∷ f (VCS vcs) ≺-split -- it
    ... | put _ &reveal _ if _ ⇒ cs  = c ∷ f (CS cs) ≺-put -- it
    ... | withdraw _                 = c ∷ []

subterms′ (C c) with c
... | _       ⇒ d                = subterms′ (C d)
... | after _ ⇒ d                = subterms′ (C d)
... | split vcs                  = subterms′ (VCS vcs)
... | put _ &reveal _ if _ ⇒ cs  = subterms′ (CS cs)
... | withdraw _                 = []
subterms′ (CS [])                = []
subterms′ (CS (c ∷ cs))          = c ∷ subterms′ (C c) ++ subterms′ (CS cs)
subterms′ (VCS [])               = []
subterms′ (VCS ((_ , cs) ∷ vcs)) = subterms′ (CS cs) ++ subterms′ (VCS vcs)

subtermsᵈ′ subtermsᵈ⁺ subtermsᵈ : Contract → List Contract
subtermsᵈ′ = subterms′ ∘ C
subtermsᵈ⁺ = subterms⁺ ∘ C
subtermsᵈ  = subterms  ∘ C
-- {-# DISPLAY subterms′ (C c) = subtermsᵈ′ c #-}

subtermsᶜ′ subtermsᶜ⁺ subtermsᶜ : Contracts → List Contract
subtermsᶜ′ = subterms′ ∘ CS
subtermsᶜ⁺ = subterms⁺ ∘ CS
subtermsᶜ  = subterms  ∘ CS
-- {-# DISPLAY subtermsᶜ′ cs = subterms′ (CS cs) #-}

subtermsᵛ′ subtermsᵛ⁺ subtermsᵛ : VContracts → List Contract
subtermsᵛ′ = subterms′ ∘ VCS
subtermsᵛ⁺ = subterms⁺ ∘ VCS
subtermsᵛ  = subterms  ∘ VCS
-- {-# DISPLAY subterms′ (VCS vcs) = subtermsᵛ′ vcs #-}

subtermsᵃ subtermsᵃ⁺ : Advertisement → List Contract
subtermsᵃ  (⟨ _ ⟩ c) = subtermsᶜ  c
subtermsᵃ⁺ (⟨ _ ⟩ c) = subtermsᶜ⁺ c

postulate
  subtermsᶜ⁺-refl : ds ⊆ subtermsᶜ⁺ ds
  subtermsᶜ′-trans : ds ⊆ subtermsᶜ′ ds′ → subtermsᶜ′ ds ⊆ subtermsᶜ′ ds′
-- subtermsᶜ′-trans ds⊆ = {!!}

h-subᵈ :
    d ∈ subtermsᵈ′ d′
    --------------------------------------
  → removeTopDecorations d ∈ subtermsᵈ⁺ d′

h-subᶜ :
    d ∈ subtermsᶜ′ ds
    --------------------------------------
  → removeTopDecorations d ∈ subtermsᶜ⁺ ds

h-subᵛ :
    d ∈ subtermsᵛ′ vcs
    --------------------------------------
  → removeTopDecorations d ∈ subtermsᵛ⁺ vcs

h-subᵈ {d} {put _ &reveal _ if _ ⇒ cs} d∈ = there $ h-subᶜ {ds = cs} d∈
h-subᵈ {d} {split vcs}                 d∈ = there $ h-subᵛ {vcs = vcs} d∈
h-subᵈ {d} {_       ⇒ d′} d∈ = h-subᵈ {d′ = d′} d∈
h-subᵈ {d} {after _ ⇒ d′} d∈ = h-subᵈ {d′ = d′} d∈

h-subᶜ {.d} {d ∷ ds} (here refl)
  with d
... | put _ &reveal _ if _ ⇒ _ = here refl
... | withdraw _               = here refl
... | split _                  = here refl
... | _       ⇒ d′ = h-subᶜ {ds = d′ ∷ ds} (here refl)
... | after _ ⇒ d′ = h-subᶜ {ds = d′ ∷ ds} (here refl)
h-subᶜ {d} {d′ ∷ ds} (there d∈)
  with ∈-++⁻ (subtermsᵈ′ d′) d∈
... | inj₂ d∈ʳ = ∈-++⁺ʳ (subtermsᵈ⁺ d′) (h-subᶜ {ds = ds} d∈ʳ)
... | inj₁ d∈ˡ
  with d′ | d∈ˡ
... | put _ &reveal _ if _ ⇒ cs | d∈ˡ′ = there $ ∈-++⁺ˡ $ h-subᶜ {ds = cs} d∈ˡ′
... | split vcs                 | d∈ˡ′ = there $ ∈-++⁺ˡ $ h-subᵛ {vcs = vcs} d∈ˡ′
... | _       ⇒ d″ | d∈ˡ′ = ∈-++⁺ˡ $ h-subᵈ {d′ = d″} d∈ˡ′
... | after _ ⇒ d″ | d∈ˡ′ = ∈-++⁺ˡ $ h-subᵈ {d′ = d″} d∈ˡ′

h-subᵛ {d} {(_ , cs) ∷ vcs} d∈
  with ∈-++⁻ (subtermsᶜ′ cs) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ $ h-subᶜ {ds = cs} d∈ˡ
... | inj₂ d∈ʳ = ∈-++⁺ʳ (subtermsᶜ⁺ cs) $ h-subᵛ {vcs = vcs} d∈ʳ

-- Lemmas about `subterms`

↦-∈ : ∀ {R : Contract → Set}
  → (∀ {d} → d ∈ ds → subterms⁺ (C d) ↦′ R)
  → subterms⁺ (CS ds) ↦′ R
↦-∈ {ds = c ∷ cs} f x∈
  with ∈-++⁻ (subterms⁺ (C c)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ (f ∘ there) x∈ʳ

↦-∈ᵛ : ∀ {R : Contract → Set}
  → (∀ {cs} → cs ∈ map proj₂ vcs → subterms⁺ (CS cs) ↦′ R)
  → subterms⁺ (VCS vcs) ↦′ R
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
