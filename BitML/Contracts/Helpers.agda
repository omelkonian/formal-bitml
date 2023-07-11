------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Lists.Collections
open import Prelude.Bifunctor
open import Prelude.General
open import Prelude.Null

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.Helpers ⋯ (let open ⋯ ⋯) where

open import BitML.Contracts.Types ⋯ hiding (C; d)
open import BitML.Contracts.Induction ⋯

PutComponent = Ids × Secrets × Predicate

removeTopDecorations : Branch → Branch
removeTopDecorations (_       ⇒ d) = removeTopDecorations d
removeTopDecorations (after _ ⇒ d) = removeTopDecorations d
removeTopDecorations d             = d

removeTopDecorations-idemp : Alg≡.IdempotentFun removeTopDecorations
removeTopDecorations-idemp = λ where
  (_ ⇒ d)       → removeTopDecorations-idemp d
  (after _ ⇒ d) → removeTopDecorations-idemp d
  (withdraw _)               → refl
  (put _ &reveal _ if _ ⇒ _) → refl
  (split _)                  → refl

----------------------
-- ** Module "macros"

-- selecting a sub-contract and stripping decorations
module ∣SELECT (c : Contract) (i : Index c) where
  d  = c ‼ i
  d∗ = removeTopDecorations d

open import BitML.Contracts.Types ⋯ using (d)

----------------
-- ** Collectors

-- T0D0 use Type'.nub on all results? or only on use-sites

private variable X : Type

mkCollect : (∀ e → (∀ e′ → e′ ≺ D e → List X) → List X) → ℂ → List X
mkCollect {X = X} mk = ≺-rec _ go
  where
    go : ∀ c → (∀ c′ → c′ ≺ c → List X) → List X
    go (D c)     f = mk c f
    go (C cs)    f = concat $ mapWith∈ cs (f (D _) ∘ ≺-∈)
    go (VCS vcs) f = concat $ mapWith∈ (map proj₂ vcs) (f (C _) ∘ ≺-∈ᵛ)

instance
  -- Hℂ : ⦃ _ : Branch has X ⦄ → ℂ has X
  -- Hℂ .collect = mkCollect (λ e _ → collect e)

  Hℂ : ⦃ _ : Branch has X ⦄ ⦃ _ : Contract has X ⦄ ⦃ _ : VContracts has X ⦄ → ℂ has X
  Hℂ .collect 𝕔 with 𝕔
  ... | D   d   = collect d
  ... | C   c   = collect c
  ... | VCS vcs = collect vcs

-- participants

participantsℂ : ℂ → List Participant
participantsℂ = mkCollect go
  where
    go : ∀ e → (∀ e′ → e′ ≺ D e → List Participant) → List Participant
    go d f with d
    ... | put _ &reveal _ if _ ⇒ c = f (C c) ≺-put -- it
    ... | withdraw p               = [ p ]
    ... | split vcs                = f (VCS vcs) ≺-split -- it
    ... | p ⇒ d′                   = p ∷ f (D d′) ≺-auth -- it
    ... | after _ ⇒ d′             = f (D d′) ≺-after -- it

instance
  HPᵈ : Branch has Participant
  HPᵈ .collect = participantsℂ ∘ D

  HPᶜ : Contract has Participant
  HPᶜ .collect = participantsℂ ∘ C

  HPᵛ : VContracts has Participant
  HPᵛ .collect = participantsℂ ∘ VCS

  HPᵖ : Precondition has Participant
  HPᵖ .collect pr with pr
  ... | p :? _ at _ = [ p ]
  ... | p :! _ at _ = [ p ]
  ... | p :secret _ = [ p ]
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HPᵃ : Ad has Participant
  -- HPᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c
  HPᵃ .collect = collect ∘ G

participants nub-participants : ⦃ _ :  X has Participant ⦄ → X → List Participant
participants = collect
nub-participants = nub ∘ participants

-- names

namesℂ : ℂ → List Name
namesℂ = mkCollect go
  where
    go : ∀ e → (∀ e′ → e′ ≺ D e → List Name) → List Name
    go d f with d
    ... | put xs &reveal as if _ ⇒ c = map inj₂ xs ++ map inj₁ as ++ f (C c) ≺-put -- it
    ... | withdraw _                 = []
    ... | split vcs                  = f (VCS vcs) ≺-split -- it
    ... | _ ⇒ d′                     = f (D d′) ≺-auth -- it
    ... | after _ ⇒ d′               = f (D d′) ≺-after -- it

instance
  HNᵈ : Branch has Name
  HNᵈ .collect = namesℂ ∘ D

  HNᶜ : Contract has Name
  HNᶜ .collect = namesℂ ∘ C

  HNᵛ : VContracts has Name
  HNᵛ .collect = namesℂ ∘ VCS

  HNᵖ : Precondition has Name
  HNᵖ .collect pr with pr
  ... | _ :? _ at x = [ inj₂ x ]
  ... | _ :! _ at x = [ inj₂ x ]
  ... | _ :secret a = [ inj₁ a ]
  ... | p₁ ∣∣ p₂    = collect p₁ ++ collect p₂

  HNᵃ : Ad has Name
  -- HNᵃ .collect (⟨ g ⟩ c) = collect g ++ collect c
  HNᵃ .collect = collect ∘ G

  HSᵃʳ : Arith has Name
  HSᵃʳ .collect ar with ar
  ... | ` _    = []
  ... | ∣ s ∣  = [ inj₁ s ]
  ... | x `+ y = collect x ++ collect y
  ... | x `- y = collect x ++ collect y

  Hᵖʳ : ⦃ _ :  Arith has X ⦄ → Predicate has X
  Hᵖʳ .collect pr with pr
  ... | `true   = []
  ... | x `∧ y  = collect x ++ collect y
  ... | `¬ x    = collect x
  ... | x `= y  = collect x ++ collect y
  ... | x `< y  = collect x ++ collect y


names : ⦃ _ :  X has Name ⦄ → X → Names
names = collect

namesˡ : ⦃ _ :  X has Name ⦄ → X → Secrets
namesˡ = filter₁ ∘ names

namesʳ : ⦃ _ :  X has Name ⦄ → X → Ids
namesʳ = filter₂ ∘ names

secrets = namesˡ
ids     = namesʳ

-- put components

putComponentsℂ : ℂ → List PutComponent
putComponentsℂ = mkCollect go
  where
    go : ∀ d → (∀ d′ → d′ ≺ D d → List PutComponent) → List PutComponent
    go d f with d
    ... | put xs &reveal as if p ⇒ c = (xs , as , p) ∷ f (C c) ≺-put -- it
    ... | withdraw _                 = []
    ... | split vcs                  = f (VCS vcs) ≺-split -- it
    ... | _ ⇒ d′                     = f (D d′) ≺-auth -- it
    ... | after _ ⇒ d′               = f (D d′) ≺-after -- it

instance
  HPCᵈ : Branch has PutComponent
  HPCᵈ .collect = putComponentsℂ ∘ D

  HPCᶜ : Contract has PutComponent
  HPCᶜ .collect = putComponentsℂ ∘ C

  HPCᵛ : VContracts has PutComponent
  HPCᵛ .collect = putComponentsℂ ∘ VCS

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

  HTDᵃ : Ad has TDepositRef
  HTDᵃ .collect = collect ∘ G

  HDᵃ : Ad has DepositRef
  HDᵃ .collect = map proj₂ ∘ collect

tdeposits : ⦃ _ :  X has TDepositRef ⦄ → X → List TDepositRef
tdeposits = collect

deposits : ⦃ _ :  X has DepositRef ⦄ → X → List DepositRef
deposits ⦃ hd ⦄ = collect ⦃ hd ⦄

private
  -- ** check that we get all accessors we want
  ∀C : Type → Type
  ∀C A = (Branch → List A) × (Contract → List A) × (VContracts → List A)

  ∀P : Type → Type
  ∀P A = (Precondition → List A) × (Ad → List A)

  ∀∀ : Type → Type
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
names⊆secretsOf {a}{g = A :secret .a} (here refl) rewrite ≟-refl A = here refl
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

decorations⊎ : Branch → List (Participant ⊎ Time)
decorations⊎ (A       ⇒ d) = inj₁ A ∷ decorations⊎ d
decorations⊎ (after t ⇒ d) = inj₂ t ∷ decorations⊎ d
decorations⊎ _             = []

decorations : Branch → List Participant × List Time
decorations c = partitionSums (decorations⊎ c)

authDecorations : Branch → List Participant
authDecorations = proj₁ ∘ decorations

timeDecorations : Branch → List Time
timeDecorations = proj₂ ∘ decorations

auth⊆part : authDecorations d ⊆ participants d
auth⊆part {d = d₀} with d₀
... | put _ &reveal _ if _ ⇒ _ = λ ()
... | withdraw _               = λ ()
... | split _                  = λ ()
... | p ⇒ d                    = λ{ (here refl) → here refl; (there p∈)  → there $ auth⊆part {d = d} p∈ }
... | after _ ⇒ d              = auth⊆part {d = d}

decorations∘remove≡[] : decorations⊎ (removeTopDecorations d) ≡ []
decorations∘remove≡[] {_ ⇒ d}       = decorations∘remove≡[] {d}
decorations∘remove≡[] {after _ ⇒ d} = decorations∘remove≡[] {d}
decorations∘remove≡[] {withdraw _} = refl
decorations∘remove≡[] {split _} = refl
decorations∘remove≡[] {put _ &reveal _ if _ ⇒ _} = refl

authDecorations∘remove≡[] : Null $ authDecorations $ removeTopDecorations d
authDecorations∘remove≡[] {d} rewrite decorations∘remove≡[] {d} = refl

timeDecorations∘remove≡[] : Null $ authDecorations $ removeTopDecorations d
timeDecorations∘remove≡[] {d} rewrite decorations∘remove≡[] {d} = refl

infix 0 _≡⋯∶_
_≡⋯∶_ : Rel₀ Branch
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

subterms subterms⁺ subterms′ : ℂ → Contract

subterms c@(D _)   = drop 1 $ subterms⁺ c
subterms c@(C _)   = subterms⁺ c
subterms c@(VCS _) = subterms⁺ c

subterms⁺ = mkCollect go
  where
    go : ∀ d → (∀ d′ → d′ ≺ D d → Contract) → Contract
    go d f with d
    ... | _       ⇒ d              = f (D d) ≺-auth -- it
    ... | after _ ⇒ d              = f (D d) ≺-after -- it
    ... | split vcs                = d ∷ f (VCS vcs) ≺-split -- it
    ... | put _ &reveal _ if _ ⇒ c = d ∷ f (C c) ≺-put -- it
    ... | withdraw _               = d ∷ []

subterms′ (D d) with d
... | _       ⇒ d              = subterms′ (D d)
... | after _ ⇒ d              = subterms′ (D d)
... | split vcs                = subterms′ (VCS vcs)
... | put _ &reveal _ if _ ⇒ c = subterms′ (C c)
... | withdraw _               = []
subterms′ (C [])                = []
subterms′ (C (d ∷ c))           = d ∷ subterms′ (D d) ++ subterms′ (C c)
subterms′ (VCS [])              = []
subterms′ (VCS ((_ , c) ∷ vcs)) = subterms′ (C c) ++ subterms′ (VCS vcs)

subtermsᵈ′ subtermsᵈ⁺ subtermsᵈ : Branch → List Branch
subtermsᵈ′ = subterms′ ∘ D
subtermsᵈ⁺ = subterms⁺ ∘ D
subtermsᵈ  = subterms  ∘ D
-- {-# DISPLAY subterms′ (C c) = subtermsᵈ′ c #-}

subtermsᶜ′ subtermsᶜ⁺ subtermsᶜ : Contract → List Branch
subtermsᶜ′ = subterms′ ∘ C
subtermsᶜ⁺ = subterms⁺ ∘ C
subtermsᶜ  = subterms  ∘ C
-- {-# DISPLAY subtermsᶜ′ cs = subterms′ (CS cs) #-}

subtermsᵛ′ subtermsᵛ⁺ subtermsᵛ : VContracts → List Branch
subtermsᵛ′ = subterms′ ∘ VCS
subtermsᵛ⁺ = subterms⁺ ∘ VCS
subtermsᵛ  = subterms  ∘ VCS
-- {-# DISPLAY subterms′ (VCS vcs) = subtermsᵛ′ vcs #-}

subtermsᵃ′ subtermsᵃ⁺ subtermsᵃ : Ad → List Branch
subtermsᵃ′ (⟨ _ ⟩ c) = subtermsᶜ′ c
subtermsᵃ⁺ (⟨ _ ⟩ c) = subtermsᶜ⁺ c
subtermsᵃ  (⟨ _ ⟩ c) = subtermsᶜ  c

{-
_ : subtermsᵈ⁺ (put xs &reveal as if p ⇒ c) ≡ (put xs &reveal as if p ⇒ c) ∷ subtermsᶜ⁺ c
_ = refl

_ : subtermsᵈ⁺ (A ⇒ d) ≡ subtermsᵈ⁺ d
_ = refl

_ : subtermsᵈ⁺ (split vcs) ≡ split vcs ∷ subtermsᵛ⁺ vcs
_ = refl

subterms⊆ : ∀ 𝕔 → subterms⁺ 𝕔 ⊆ subterms′ 𝕔
subterms⊆ (C (put x &reveal x₁ if x₂ ⇒ x₃)) = {!!}
subterms⊆ (C (withdraw x)) = {!!}
subterms⊆ (C (split x)) = {!!}
subterms⊆ (C (x ⇒ c)) = {!!}
subterms⊆ (C (after x ⇒ c)) = {!!}
subterms⊆ (CS  cs)  = {!!}
subterms⊆ (VCS vcs) = {!!}

subterms⊆∗ : removeTopDecorations d ∈ subtermsᶜ′ [ removeTopDecorations d ]
subterms⊆∗ {put x &reveal x₁ if x₂ ⇒ x₃} = here refl
subterms⊆∗ {withdraw x} = here refl
subterms⊆∗ {split x} = here refl
subterms⊆∗ {x ⇒ d} rewrite L.++-identityʳ (subtermsᵈ′ d) = there (∈-++⁺ˡ {!subterms⊆∗ {d}!})
subterms⊆∗ {after x ⇒ d} = there {!!}

mutual
  subterms⁺⊆ᵈ′ : subtermsᵈ⁺ d ⊆ removeTopDecorations d ∷ subtermsᵈ′ d
  subterms⁺⊆ᵈ′ {put _ &reveal _ if _ ⇒ c} = λ where
    (here refl) → here refl
    (there x∈)  → there (subterms⁺⊆ᶜ′ {c} x∈)
  subterms⁺⊆ᵈ′ {withdraw _} = λ where
    (here refl) → here refl
  subterms⁺⊆ᵈ′ {split vcs} = λ where
    (here refl) → here refl
    (there x∈)  → there (subterms⁺⊆ᵛ′ {vcs} x∈)
  subterms⁺⊆ᵈ′ {_ ⇒ d} = subterms⁺⊆ᵈ′ {d}
  subterms⁺⊆ᵈ′ {after _ ⇒ d} = subterms⁺⊆ᵈ′ {d}

  subterms⁺⊆ᶜ′ : subtermsᶜ⁺ c ⊆ subtermsᶜ′ c
  subterms⁺⊆ᶜ′ {[]} = id
  subterms⁺⊆ᶜ′ {d ∷ ds} =
    begin⊆ subtermsᶜ⁺ (d ∷ ds) ≡⟨⟩
          subtermsᵈ⁺ d ++ subtermsᶜ⁺ ds ⊆⟨ {!!} ⟩
          (d∗ ∷ subtermsᵈ′ d) ++ subtermsᶜ′ ds
          d ∷ subtermsᵈ′ d ++ subtermsᶜ′ ds ≡⟨⟩
          subtermsᶜ′ (d ∷ ds) ⊆∎
    where open ⊆-Reasoning Branch renaming (begin_ to begin⊆_; _∎ to _⊆∎)

  subterms⁺⊆ᵛ′ : subtermsᵛ⁺ vcs ⊆ subtermsᵛ′ vcs
  subterms⁺⊆ᵛ′ {[]} = id
  subterms⁺⊆ᵛ′ {(v , c) ∷ vcs} =
    begin⊆ subtermsᵛ⁺ ((v , c) ∷ vcs) ≡⟨⟩
           subtermsᶜ⁺ c ++ subtermsᵛ⁺ vcs ⊆⟨ {!!} ⟩
           subtermsᶜ′ c ++ subtermsᵛ′ vcs ≡⟨⟩
           subtermsᵛ′ ((v , c) ∷ vcs) ⊆∎
    where open ⊆-Reasoning Branch renaming (begin_ to begin⊆_; _∎ to _⊆∎)
-}

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

h-sub∗ : subtermsᵈ′ (removeTopDecorations d) ⊆ subtermsᵈ′ d
h-sub∗ {_ ⇒ d} = h-sub∗ {d}
h-sub∗ {after _ ⇒ d} = h-sub∗ {d}
h-sub∗ {put _ &reveal _ if _ ⇒ _} = id
h-sub∗ {withdraw _} = id
h-sub∗ {split _} = id

h-sub‼ : ∀ {i : Index c} → subtermsᵈ′ (removeTopDecorations (c ‼ i)) ⊆ subtermsᶜ′ c
h-sub‼ {d ∷ _} {0F}     = there ∘ ∈-++⁺ˡ                ∘ h-sub∗ {d}
h-sub‼ {d ∷ c} {fsuc i} = there ∘ ∈-++⁺ʳ (subtermsᵈ′ d) ∘ h-sub‼ {c}{i}

-- Lemmas about `subterms`

↦-∈ : ∀ {R : Branch → Type}
  → (∀ {d} → d ∈ ds → subterms⁺ (D d) ↦′ R)
  → subterms⁺ (C ds) ↦′ R
↦-∈ {ds = d ∷ ds} f x∈
  with ∈-++⁻ (subterms⁺ (D d)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ (f ∘ there) x∈ʳ

↦-∈ᵛ : ∀ {R : Branch → Type}
  → (∀ {c} → c ∈ map proj₂ vcs → subterms⁺ (C c) ↦′ R)
  → subterms⁺ (VCS vcs) ↦′ R
↦-∈ᵛ {vcs = (_ , c) ∷ vcs} f x∈
  with ∈-++⁻ (subterms⁺ (C c)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ᵛ (f ∘ there) x∈ʳ

mutual
  subterms⊆ᶜ : ds ⊆ subterms′ (C ds)
  subterms⊆ᶜ {ds = d ∷ ds} (here refl) = here refl
  subterms⊆ᶜ {ds = d ∷ ds} (there d∈)  = there $ ∈-++⁺ʳ (subterms′ $ D d) (subterms⊆ᶜ d∈)

  subterms⊆ᵛ : (v , c) ∈ vcs → c ⊆ subterms′ (VCS vcs)
  subterms⊆ᵛ {vcs = (_ , c) ∷ vcs} (here refl) = ∈-++⁺ˡ ∘ subterms⊆ᶜ
  subterms⊆ᵛ {vcs = (_ , c) ∷ vcs} (there p)   = ∈-++⁺ʳ (subterms′ $ C c) ∘ subterms⊆ᵛ p

  subterms⊆ᵛ′ : c ∈ map proj₂ vcs → subtermsᶜ′ c ⊆ subtermsᵈ′ (split vcs)
  subterms⊆ᵛ′ {vcs = (v , c) ∷ _}   (here refl) = ∈-++⁺ˡ
  subterms⊆ᵛ′ {vcs = (v , c) ∷ vcs} (there c∈)  = ∈-++⁺ʳ _ ∘ subterms⊆ᵛ′ {vcs = vcs} c∈

  subterms⊆ᵛᶜⁱˢ : ∀ {vcis : List (Value × Contract × Id)} → let (vs , cs , ys) = unzip₃ vcis in
      c ∈ cs
    → subtermsᶜ′ c ⊆ subtermsᵈ′ (split $ zip vs cs)
  subterms⊆ᵛᶜⁱˢ {vcis = (v , c , _) ∷ _}    (here refl)
    = ∈-++⁺ˡ
  subterms⊆ᵛᶜⁱˢ {vcis = (v , c , _) ∷ vcis} (there c∈)
    = ∈-++⁺ʳ _ ∘ subterms⊆ᵛᶜⁱˢ {vcis = vcis} c∈

mutual
  subterms′-names⊆ᵈ : d ∈ subterms′ (D d′) → names d ⊆ names d′
  subterms′-names⊆ᵈ {d′ = d} with d
  ... | put xs &reveal as if _ ⇒ ds = λ x∈ → ∈-++⁺ʳ (map inj₂ xs) ∘ ∈-++⁺ʳ (map inj₁ as) ∘ subterms′-names⊆ᶜ {ds = ds} x∈
  ... | withdraw _                  = λ ()
  ... | split vcs                   = subterms′-names⊆ᵛ {vcs = vcs}
  ... | _ ⇒ d′                      = subterms′-names⊆ᵈ {d′ = d′}
  ... | after _ ⇒ d′                = subterms′-names⊆ᵈ {d′ = d′}

  subterms′-names⊆ᶜ : d ∈ subterms′ (C ds) → names d ⊆ names ds
  subterms′-names⊆ᶜ {ds = d ∷ ds} (here refl) = ∈-++⁺ˡ
  subterms′-names⊆ᶜ {ds = d ∷ ds} (there p)
    with ∈-++⁻ _ p
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᶜ {ds = ds} p′
  ... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-names⊆ᵈ {d′ = d} p′

  subterms′-names⊆ᵛ : d ∈ subterms′ (VCS vcs) → names d ⊆ names vcs
  subterms′-names⊆ᵛ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᵛ {vcs = vcs} p
  subterms′-names⊆ᵛ {vcs = (_ , ds) ∷ vcs} p
    with ∈-++⁻ (subterms′ $ C ds) p
  ... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-names⊆ᶜ {ds = ds} p′
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᵛ {vcs = vcs} p′

mutual
  subterms′-putComponents⊆ᵈ : d ∈ subterms′ (D d′) → putComponents d ⊆ putComponents d′
  subterms′-putComponents⊆ᵈ {d′ = d} with d
  ... | put _ &reveal _ if _ ⇒ ds = λ x∈ → there ∘ subterms′-putComponents⊆ᶜ {ds = ds} x∈
  ... | withdraw _                = λ ()
  ... | split vcs                 = subterms′-putComponents⊆ᵛ {vcs = vcs}
  ... | _ ⇒ d′                    = subterms′-putComponents⊆ᵈ {d′ = d′}
  ... | after _ ⇒ d′              = subterms′-putComponents⊆ᵈ {d′ = d′}

  subterms′-putComponents⊆ᶜ : d ∈ subterms′ (C ds) → putComponents d ⊆ putComponents ds
  subterms′-putComponents⊆ᶜ {ds = _ ∷ _}  (here refl) = ∈-++⁺ˡ
  subterms′-putComponents⊆ᶜ {ds = d ∷ ds} (there p)
    with ∈-++⁻ _ p
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᶜ {ds = ds} p′
  ... | inj₁ p′ = ∈-++⁺ˡ   ∘ subterms′-putComponents⊆ᵈ  {d′ = d} p′

  subterms′-putComponents⊆ᵛ : d ∈ subterms′ (VCS vcs) → putComponents d ⊆ putComponents vcs
  subterms′-putComponents⊆ᵛ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᵛ {vcs = vcs} p
  subterms′-putComponents⊆ᵛ {vcs = (_ , ds) ∷ vcs} p
    with ∈-++⁻ (subterms′ $ C ds) p
  ... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-putComponents⊆ᶜ {ds = ds} p′
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᵛ {vcs = vcs} p′

mutual
  subterms′-part⊆ᵈ : d ∈ subtermsᵈ′ d′ → participants d ⊆ participants d′
  subterms′-part⊆ᵈ {d′ = d} with d
  ... | put _ &reveal _ if _ ⇒ ds = subterms′-part⊆ᶜ {ds = ds}
  ... | withdraw _                = λ ()
  ... | split vcs                 = subterms′-part⊆ᵛ {vcs = vcs}
  ... | _ ⇒ d′                    = λ x∈ → there ∘ subterms′-part⊆ᵈ {d′ = d′} x∈
  ... | after _ ⇒ d′              = subterms′-part⊆ᵈ {d′ = d′}

  subterms′-part⊆ᶜ : d ∈ subtermsᶜ′ ds → participants d ⊆ participants ds
  subterms′-part⊆ᶜ {ds = d ∷ ds} (here refl) = ∈-++⁺ˡ
  subterms′-part⊆ᶜ {ds = d ∷ ds} (there p)
    with ∈-++⁻ _ p
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-part⊆ᶜ {ds = ds} p′
  ... | inj₁ p′ = ∈-++⁺ˡ   ∘ subterms′-part⊆ᵈ {d′ = d} p′

  subterms′-part⊆ᵛ : d ∈ subtermsᵛ′ vcs → participants d ⊆ participants vcs
  subterms′-part⊆ᵛ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-part⊆ᵛ {vcs = vcs} p
  subterms′-part⊆ᵛ {vcs = (_ , ds) ∷ vcs} p
    with ∈-++⁻ (subterms′ $ C ds) p
  ... | inj₁ p′ = ∈-++⁺ˡ   ∘ subterms′-part⊆ᶜ {ds = ds} p′
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-part⊆ᵛ {vcs = vcs} p′
