------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init
open import Prelude.Lists as L hiding (_↦_; _↦′_)
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.SetCollections
open import Prelude.Bifunctor
open import Prelude.General
open import Prelude.Sets
open import Prelude.FromList
open import Prelude.ToList
open import Prelude.Null
open import Prelude.InferenceRules

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest hiding (C; d)
open import BitML.Contracts.Induction Participant Honest

PutComponent = Ids × Secrets × Predicate

removeTopDecorations : Contract → Contract
removeTopDecorations = λ where
  (_       ⇒ d) → removeTopDecorations d
  (after _ ⇒ d) → removeTopDecorations d
  d             → d

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
module ∣SELECT (c : Contracts) (i : Index c) where
  d  = c ‼ i
  d∗ = removeTopDecorations d

open import BitML.Contracts.Types Participant Honest using (d)

----------------
-- ** Collectors

module _ {X : Set} ⦃ _ : DecEq X ⦄ where

  mkCollect : (∀ e → (∀ e′ → e′ ≺ C e → List X) → List X) → ℂ → Set⟨ X ⟩
  mkCollect mk = fromList ∘ mkCollectList
    module _ where
      mkCollectList : ℂ → List X
      mkCollectList = ≺-rec _ go
        where
          go : ∀ c → (∀ c′ → c′ ≺ c → List X) → List X
          go (C c)     f = mk c f
          go (CS cs)   f = concat $ mapWith∈ cs (f (C _) ∘ ≺-∈)
          go (VCS vcs) f = concat $ mapWith∈ (map proj₂ vcs) (f (CS _) ∘ ≺-∈ᵛ)


  instance
    Hℂ : ⦃ _ : Contract has X ⦄ → ℂ has X
    Hℂ .collect = mkCollect (λ e _ → collectList e)

-- participants

participantsℂ : ℂ → Set⟨ Participant ⟩
participantsℂ = mkCollect go
  module ∣participantsℂ∣ where
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
  ... | p :? _ at _ = singleton p
  ... | p :! _ at _ = singleton p
  ... | p :secret _ = singleton p
  ... | p₁ ∣∣ p₂    = collect p₁ ∪ collect p₂

  HPᵃ : Advertisement has Participant
  HPᵃ .collect = collect ∘ G

-- names

namesℂ : ℂ → Set⟨ Name ⟩
namesℂ = mkCollect go
  module ∣namesℂ∣ where
    go : ∀ e → (∀ e′ → e′ ≺ C e → List Name) → List Name
    go c f with c
    ... | put xs &reveal as if _ ⇒ cs =
      map inj₂ (toList xs) ++ map inj₁ (toList as) ++ f (CS cs) ≺-put
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
  ... | _ :? _ at x = singleton (inj₂ x)
  ... | _ :! _ at x = singleton (inj₂ x)
  ... | _ :secret a = singleton (inj₁ a)
  ... | p₁ ∣∣ p₂    = collect p₁ ∪ collect p₂

  HNᵃ : Advertisement has Name
  HNᵃ .collect = collect ∘ G

  HSᵃʳ : Arith has Name
  HSᵃʳ .collect ar with ar
  ... | ` _    = ∅
  ... | ∣ s ∣  = singleton (inj₁ s)
  ... | x `+ y = collect x ∪ collect y
  ... | x `- y = collect x ∪ collect y

-- put components

putComponentsℂ : ℂ → Set⟨ PutComponent ⟩
putComponentsℂ = mkCollect go
  module ∣putComponentsℂ∣ where
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

-- deposits

instance
  HTDᵖ : Precondition has TDepositRef
  HTDᵖ .collect pr with pr
  ... | p :? v at x = singleton (volatile   , p , v , x)
  ... | p :! v at x = singleton (persistent , p , v , x)
  ... | _ :secret _ = ∅
  ... | p₁ ∣∣ p₂    = collect p₁ ∪ collect p₂

  HDᵖ : Precondition has DepositRef
  -- HDᵖ .collect = mapˢ proj₂ ∘ collect
  HDᵖ .collect pr with pr
  ... | p :? v at x = singleton (p , v , x)
  ... | p :! v at x = singleton (p , v , x)
  ... | _ :secret _ = ∅
  ... | p₁ ∣∣ p₂    = collect p₁ ∪ collect p₂

  HTDᵃ : Advertisement has TDepositRef
  HTDᵃ .collect = collect ∘ G

  HDᵃ : Advertisement has DepositRef
  -- HDᵃ .collect = mapˢ proj₂ ∘ collect
  HDᵃ .collect = collect ∘ G

module _ {X : Set} where
  names : ⦃ _ :  X has Name ⦄ → X → Names
  names = collect

  namesˡ : ⦃ _ :  X has Name ⦄ → X → Secrets
  namesˡ = filterˢ₁ ∘ names

  namesʳ : ⦃ _ :  X has Name ⦄ → X → Ids
  namesʳ = filterˢ₂ ∘ names

  secrets = namesˡ
  ids     = namesʳ

  putComponents : ⦃ _ :  X has PutComponent ⦄ → X → Set⟨ PutComponent ⟩
  putComponents = collect

  tdeposits : ⦃ _ :  X has TDepositRef ⦄ → X → Set⟨ TDepositRef ⟩
  tdeposits = collect

  deposits : ⦃ _ :  X has DepositRef ⦄ → X → Set⟨ DepositRef ⟩
  deposits = collect

  participants : ⦃ _ :  X has Participant ⦄ → X → Set⟨ Participant ⟩
  participants = collect

  instance
    Hᵖʳ : ⦃ _ : DecEq X ⦄ ⦃ _ :  Arith has X ⦄ → Predicate has X
    Hᵖʳ .collect pr with pr
    ... | `true   = ∅
    ... | x `∧ y  = collect x ∪ collect y
    ... | `¬ x    = collect x
    ... | x `= y  = collect x ∪ collect y
    ... | x `< y  = collect x ∪ collect y

-- ** check that we get all accessors we want
private
  module _ (A : Set) ⦃ _ : DecEq A ⦄ where
    ∀C = (Contract → Set⟨ A ⟩) × (Contracts → Set⟨ A ⟩) × (VContracts → Set⟨ A ⟩)
    ∀P = (Precondition → Set⟨ A ⟩) × (Advertisement → Set⟨ A ⟩)
    ∀∀ = ∀C × ∀P

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
  module ∣secretsOfᵖ∣ where
    go : Precondition → Secrets
    go (B :secret s) with A ≟ B
    ... | yes _ = singleton s
    ... | no  _ = ∅
    go (l ∣∣ r ) = go l ∪ go r
    go _         = ∅

open ≈ˢ-Reasoning

participants≡ : participants (d ∷ ds) ≈ˢ (participants d ∪ participants ds)
participants≡ {d = d} = from-++ˢ {xs = mkCollectList ∣participantsℂ∣.go (C d)}

participants≡ᵛ : participants ((v , ds) ∷ vcs) ≈ˢ (participants ds ∪ participants vcs)
participants≡ᵛ {ds = ds} = from-++ˢ {xs = mkCollectList ∣participantsℂ∣.go (CS ds)}

participants-auth≡ : participants (A ⇒ d) ≈ˢ (A ∷ˢ participants d)
participants-auth≡ {d = d} = from-∷ˢ {xs = mkCollectList ∣participantsℂ∣.go (C d)}

namesˡ⇒part : a ∈ˢ namesˡ g → Σ Participant (_∈ˢ participants g)
namesˡ⇒part {g = _ :secret _} (here refl) = -, here refl
namesˡ⇒part {g = l ∣∣ r} =
  mapMaybeˢ-∪ isInj₁ {xs = names l}{names r} .proj₁ >≡>
  ∈-∪⁻ _ (namesˡ l) (namesˡ r) >≡> λ where
    (inj₁ a∈ˡ) → map₂′ (∈-∪⁺ˡ _ (participants l) (participants r))
               $ namesˡ⇒part {g = l} a∈ˡ
    (inj₂ a∈ʳ) → map₂′ (∈-∪⁺ʳ _ (participants l) (participants r))
               $ namesˡ⇒part {g = r} a∈ʳ

names⊆secretsOf : (a∈ : a ∈ˢ namesˡ g)
                → a ∈ˢ secretsOfᵖ (namesˡ⇒part {g = g} a∈ .proj₁) g
names⊆secretsOf {g = A :secret _} (here refl) rewrite ≟-refl A = here refl
names⊆secretsOf {g = g@(l ∣∣ r)} a∈
  with ∈-∪⁻ _ (namesˡ l) (namesˡ r)
            $ mapMaybeˢ-∪ isInj₁ {xs = names l}{names r} .proj₁ a∈
... | inj₁ a∈ˡ =
  let open ∣secretsOfᵖ∣ (namesˡ⇒part {g = l} a∈ˡ .proj₁)
  in ∈-∪⁺ˡ _ (go l) (go r) $ names⊆secretsOf {g = l} a∈ˡ
... | inj₂ a∈ʳ =
  let open ∣secretsOfᵖ∣ (namesˡ⇒part {g = r} a∈ʳ .proj₁)
  in ∈-∪⁺ʳ _ (go l) (go r) $ names⊆secretsOf {g = r} a∈ʳ

names≡ : names (d ∷ ds) ≈ˢ (names d ∪ names ds)
names≡ {d = d} = from-++ˢ {xs = mkCollectList ∣namesℂ∣.go (C d)}

names≡ᵛ : names ((v , ds) ∷ vcs) ≈ˢ (names ds ∪ names vcs)
names≡ᵛ {ds = ds} = from-++ˢ {xs = mkCollectList ∣namesℂ∣.go (CS ds)}

names-put≡ : names (put xs &reveal as if p ⇒ ds) ≈ˢ (mapˢ inj₂ xs ∪ mapˢ inj₁ as ∪ names ds)
names-put≡ {xs = xs}{as}{p}{ds} =
  begin
    names (put xs &reveal as if p ⇒ ds)
  ≡⟨⟩
    namesℂ (C $ put xs &reveal as if p ⇒ ds)
  ≡⟨⟩
    mkCollect ∣namesℂ∣.go (C $ put xs &reveal as if p ⇒ ds)
  ≡⟨⟩
    fromList (mkCollectList ∣namesℂ∣.go (C $ put xs &reveal as if p ⇒ ds))
  ≡⟨⟩
    fromList (  map inj₂ (toList xs)
             ++ map inj₁ (toList as)
             ++ mkCollectList ∣namesℂ∣.go (CS ds)
             )
  ≈⟨ from-++ˢ {xs = map inj₂ (toList xs)} ⟩
      mapˢ inj₂ xs
    ∪ fromList (  map inj₁ (toList as)
               ++ mkCollectList ∣namesℂ∣.go (CS ds)
               )
  ≈⟨ ∪-congˡ {ys = fromList $ map inj₁ (toList as) ++ mkCollectList ∣namesℂ∣.go (CS ds)}
             {zs = mapˢ inj₁ as ∪ names ds}
             {xs = mapˢ inj₂ xs}
           $ from-++ˢ {xs = map inj₁ (toList as)}
   ⟩
      mapˢ inj₂ xs ∪ mapˢ inj₁ as ∪ names ds
  ≡⟨⟩
    mapˢ inj₂ xs ∪ mapˢ inj₁ as ∪ names ds
  ∎

putComponents≡ : putComponents (d ∷ ds) ≈ˢ (putComponents d ∪ putComponents ds)
putComponents≡ {d = d} = from-++ˢ {xs = mkCollectList ∣putComponentsℂ∣.go (C d)}

putComponents≡ᵛ : putComponents ((v , ds) ∷ vcs) ≈ˢ (putComponents ds ∪ putComponents vcs)
putComponents≡ᵛ {ds = ds} = from-++ˢ {xs = mkCollectList ∣putComponentsℂ∣.go (CS ds)}

putComponents-put≡ : putComponents (put xs &reveal as if p ⇒ ds) ≈ˢ ((xs , as , p) ∷ˢ putComponents ds)
putComponents-put≡ {xs = xs}{as}{p}{ds} =
  begin
    putComponents (put xs &reveal as if p ⇒ ds)
  ≡⟨⟩
    putComponentsℂ (C $ put xs &reveal as if p ⇒ ds)
  ≡⟨⟩
    mkCollect ∣putComponentsℂ∣.go (C $ put xs &reveal as if p ⇒ ds)
  ≡⟨⟩
    fromList (mkCollectList ∣putComponentsℂ∣.go (C $ put xs &reveal as if p ⇒ ds))
  ≡⟨⟩
    fromList ((xs , as , p) ∷ mkCollectList ∣putComponentsℂ∣.go (CS ds))
  ≈⟨ from-∷ˢ {xs = mkCollectList ∣putComponentsℂ∣.go (CS ds)} ⟩
    (xs , as , p) ∷ˢ fromList (mkCollectList ∣putComponentsℂ∣.go (CS ds))
  ≡⟨⟩
    (xs , as , p) ∷ˢ putComponents ds
  ∎

-- Deposits

isVolatile isPersistent : TDepositRef → Maybe DepositRef
isVolatile = case_of λ where
  (volatile   , d) → just d
  (persistent , _) → nothing
isPersistent = case_of λ where
  (volatile   , _) → nothing
  (persistent , d) → just d

volatileDeposits persistentDeposits : Precondition → Set⟨ DepositRef ⟩
volatileDeposits   = mapMaybeˢ isVolatile   ∘ tdeposits
persistentDeposits = mapMaybeˢ isPersistent ∘ tdeposits

persistentValue : Precondition → Value
persistentValue = sumˢ ∘ mapˢ (proj₁ ∘ proj₂) ∘ persistentDeposits

volatileParticipants persistentParticipants : Precondition → Set⟨ Participant ⟩
volatileParticipants   = mapˢ proj₁ ∘ volatileDeposits
persistentParticipants = mapˢ proj₁ ∘ persistentDeposits

volatileNamesʳ persistentNamesʳ : Precondition → Ids
volatileNamesʳ   = mapˢ (proj₂ ∘ proj₂) ∘ volatileDeposits
persistentNamesʳ = mapˢ (proj₂ ∘ proj₂) ∘ persistentDeposits

volatileNames⊆ : volatileNamesʳ g ⊆ˢ namesʳ g
volatileNames⊆ {g = A :? v at x} (here refl) = ∈ˢ-singleton
volatileNames⊆ {g = l ∣∣ r}  {n} n∈
  with (p , v , .n) , d∈ , refl ←
    ∈ˢ-map⁻ (proj₂ ∘ proj₂) {xs = volatileDeposits (l ∣∣ r)} n∈
  with _ , d∈ , d≡ ← ∈ˢ-mapMaybe⁻ isVolatile {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-∪⁻ _ (tdeposits l) (tdeposits r) d∈
... | inj₁ d∈ˡ
  with (_ , m∈ , m≡) ← ∈ˢ-mapMaybe⁻ isInj₂ {xs = names l} $ volatileNames⊆ {g = l}
                     $ ∈ˢ-map⁺ (proj₂ ∘ proj₂) {xs = volatileDeposits l}
                     $ ∈ˢ-mapMaybe⁺ isVolatile {xs = tdeposits l} d∈ˡ d≡
  = ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-∪⁺ˡ _ (names l) (names r) m∈) m≡
... | inj₂ d∈ʳ
  with (_ , m∈ , m≡) ← ∈ˢ-mapMaybe⁻ isInj₂ {xs = names r} $ volatileNames⊆ {g = r}
                     $ ∈ˢ-map⁺ (proj₂ ∘ proj₂) {xs = volatileDeposits r}
                     $ ∈ˢ-mapMaybe⁺ isVolatile {xs = tdeposits r} d∈ʳ d≡
  = ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-∪⁺ʳ _ (names l) (names r) m∈) m≡

persistentNames⊆ : persistentNamesʳ g ⊆ˢ namesʳ g
persistentNames⊆ {g = A :! v at x} (here refl) = ∈ˢ-singleton
persistentNames⊆ {g = l ∣∣ r}  {n} n∈
  with (p , v , .n) , d∈ , refl ←
    ∈ˢ-map⁻ (proj₂ ∘ proj₂) {xs = persistentDeposits (l ∣∣ r)} n∈
  with _ , d∈ , d≡ ← ∈ˢ-mapMaybe⁻ isPersistent {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-∪⁻ _ (tdeposits l) (tdeposits r) d∈
... | inj₁ d∈ˡ
  with (_ , m∈ , m≡) ← ∈ˢ-mapMaybe⁻ isInj₂ {xs = names l} $ persistentNames⊆ {g = l}
                     $ ∈ˢ-map⁺ (proj₂ ∘ proj₂) {xs = persistentDeposits l}
                     $ ∈ˢ-mapMaybe⁺ isPersistent {xs = tdeposits l} d∈ˡ d≡
  = ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-∪⁺ˡ _ (names l) (names r) m∈) m≡
... | inj₂ d∈ʳ
  with (_ , m∈ , m≡) ← ∈ˢ-mapMaybe⁻ isInj₂ {xs = names r} $ persistentNames⊆ {g = r}
                     $ ∈ˢ-map⁺ (proj₂ ∘ proj₂) {xs = persistentDeposits r}
                     $ ∈ˢ-mapMaybe⁺ isPersistent {xs = tdeposits r} d∈ʳ d≡
  = ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-∪⁺ʳ _ (names l) (names r) m∈) m≡

volatileParticipants⊆ : volatileParticipants g ⊆ˢ participants g
volatileParticipants⊆ {g = A :? _ at _} (here refl) = ∈ˢ-singleton
volatileParticipants⊆ {g = l ∣∣ r} {p} p∈
  with (.p , v , x) , d∈ , refl ← ∈ˢ-map⁻ proj₁ {xs = volatileDeposits (l ∣∣ r)} p∈
  with _ , d∈ , d≡ ← ∈ˢ-mapMaybe⁻ isVolatile {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-∪⁻ _ (tdeposits l) (tdeposits r) d∈
... | inj₁ d∈ˡ = ∈-∪⁺ˡ _ (participants l) (participants r)
  ( volatileParticipants⊆ {g = l}
  $ ∈ˢ-map⁺ proj₁ {xs = volatileDeposits l}
  $ ∈ˢ-mapMaybe⁺ isVolatile {xs = tdeposits l} d∈ˡ d≡
  )
... | inj₂ d∈ʳ = ∈-∪⁺ʳ _ (participants l) (participants r)
  ( volatileParticipants⊆ {g = r}
  $ ∈ˢ-map⁺ proj₁ {xs = volatileDeposits r}
  $ ∈ˢ-mapMaybe⁺ isVolatile {xs = tdeposits r} d∈ʳ d≡
  )

persistentParticipants⊆ : persistentParticipants g ⊆ˢ participants g
persistentParticipants⊆ {g = A :! _ at _} (here refl) = ∈ˢ-singleton
persistentParticipants⊆ {g = l ∣∣ r} {p} p∈
  with (.p , v , x) , d∈ , refl ← ∈ˢ-map⁻ proj₁ {xs = persistentDeposits (l ∣∣ r)} p∈
  with _ , d∈ , d≡ ← ∈ˢ-mapMaybe⁻ isPersistent {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-∪⁻ _ (tdeposits l) (tdeposits r) d∈
... | inj₁ d∈ˡ = ∈-∪⁺ˡ _ (participants l) (participants r)
  ( persistentParticipants⊆ {g = l}
  $ ∈ˢ-map⁺ proj₁ {xs = persistentDeposits l}
  $ ∈ˢ-mapMaybe⁺ isPersistent {xs = tdeposits l} d∈ˡ d≡
  )
... | inj₂ d∈ʳ = ∈-∪⁺ʳ _ (participants l) (participants r)
  ( persistentParticipants⊆ {g = r}
  $ ∈ˢ-map⁺ proj₁ {xs = persistentDeposits r}
  $ ∈ˢ-mapMaybe⁺ isPersistent {xs = tdeposits r} d∈ʳ d≡
  )

getDeposit : namesʳ g ↦ (Σ[ d ∈ DepositRef ] (proj₁ d ∈ˢ participants g))
getDeposit {g = A :? v at x} = mk↦ λ _ → (A , v , x) , ∈ˢ-singleton
getDeposit {g = A :! v at x} = mk↦ λ _ → (A , v , x) , ∈ˢ-singleton
getDeposit {g = _ :secret _} = mk↦ λ ()
getDeposit {g = l ∣∣ r}      = mk↦ λ x∈ →
  let _ , y∈ , y≡ = ∈ˢ-mapMaybe⁻ isInj₂ {xs = names l ∪ names r} x∈
  in case ∈-∪⁻ _ (names l) (names r) y∈ of λ where
     (inj₁ x∈ˡ) → map₂′ (∈-∪⁺ˡ _ (participants l) (participants r))
                $ unmk↦ getDeposit {g = l}
                $ ∈ˢ-mapMaybe⁺ isInj₂ {xs = names l} x∈ˡ y≡
     (inj₂ x∈ʳ) → map₂′ (∈-∪⁺ʳ _ (participants l) (participants r))
                $ unmk↦ getDeposit {g = r}
                $ ∈ˢ-mapMaybe⁺ isInj₂ {xs = names r} x∈ʳ y≡

checkDeposit : DepositType → Id → Precondition → Maybe Value
checkDeposit ty x
  = headˢ ∘ mapˢ (proj₁ ∘ proj₂) ∘ filterˢ ((_≟ x) ∘ proj₂ ∘ proj₂)
  ∘ (case ty of λ{ persistent → persistentDeposits; volatile → volatileDeposits })

getName : (A , v , x) ∈ˢ persistentDeposits g
        → x ∈ˢ namesʳ g
getName {g = _ :! _ at _} (here refl) = ∈ˢ-singleton
getName {g = _ :? _ at _} ()
getName {g = l ∣∣ r}      d∈
  with _ , td∈ , td≡ ← ∈ˢ-mapMaybe⁻ isPersistent {xs = tdeposits (l ∣∣ r)} d∈
  with ∈-∪⁻ _ (tdeposits l) (tdeposits r) td∈
... | inj₁ d∈ˡ =
  let _ , y∈ , y≡ = ∈ˢ-mapMaybe⁻ isInj₂ {xs = names l}
                  $ getName {g = l}
                  $ ∈ˢ-mapMaybe⁺ isPersistent {xs = tdeposits l} d∈ˡ td≡
  in ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-∪⁺ˡ _ (names l) (names r) y∈) y≡
... | inj₂ d∈ʳ =
  let _ , y∈ , y≡ = ∈ˢ-mapMaybe⁻ isInj₂ {xs = names r}
                  $ getName {g = r}
                  $ ∈ˢ-mapMaybe⁺ isPersistent {xs = tdeposits r} d∈ʳ td≡
  in ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣∣ r)} (∈-∪⁺ʳ _ (names l) (names r) y∈) y≡

-- Decorations

decorations⊎ : Contract → Set⟨ Participant ⊎ Time ⟩
decorations⊎ (A       ⇒ d) = inj₁ A ∷ˢ decorations⊎ d
decorations⊎ (after t ⇒ d) = inj₂ t ∷ˢ decorations⊎ d
decorations⊎ _             = ∅

decorations : Contract → Set⟨ Participant ⟩ × Set⟨ Time ⟩
decorations c = partitionSumsˢ (decorations⊎ c)

authDecorations : Contract → Set⟨ Participant ⟩
authDecorations = proj₁ ∘ decorations

timeDecorations : Contract → Set⟨ Time ⟩
timeDecorations = proj₂ ∘ decorations

authDecorations-auth≡ : authDecorations (A ⇒ d) ≈ˢ (A ∷ˢ authDecorations d)
authDecorations-auth≡ {d = d} = leftsˢ∘inj₁ {abs = decorations⊎ d}

authDecorations-delay≡ : authDecorations (after t ⇒ d) ≈ˢ authDecorations d
authDecorations-delay≡ {d = d} = leftsˢ∘inj₂ {abs = decorations⊎ d}

auth⊆part : authDecorations d ⊆ˢ participants d
auth⊆part {d = put _ &reveal _ if _ ⇒ _} ()
auth⊆part {d = withdraw _} ()
auth⊆part {d = split _} ()
auth⊆part {d = p ⇒ d} {x} x∈
  with ∈ˢ-∷⁻ {xs = authDecorations d}
     $ authDecorations-auth≡ {d = d} .proj₁ x∈
... | inj₁ refl = participants-auth≡ {d = d} .proj₂ (here refl)
... | inj₂ x∈   = participants-auth≡ {d = d} .proj₂
                $ thereˢ {xs = participants d}
                $ auth⊆part {d = d} x∈
auth⊆part {after t ⇒ d} = auth⊆part {d = d}
                        ∘ authDecorations-delay≡ {t = t}{d} .proj₁

decorations∘remove≡[] : decorations⊎ (removeTopDecorations d) ≡ ∅
decorations∘remove≡[] {_ ⇒ d}       = decorations∘remove≡[] {d}
decorations∘remove≡[] {after _ ⇒ d} = decorations∘remove≡[] {d}
decorations∘remove≡[] {withdraw _} = refl
decorations∘remove≡[] {split _} = refl
decorations∘remove≡[] {put _ &reveal _ if _ ⇒ _} = refl

authDecorations∘remove≡[] : authDecorations (removeTopDecorations d) ≡ ∅
authDecorations∘remove≡[] {d} rewrite decorations∘remove≡[] {d} = refl

timeDecorations∘remove≡[] : authDecorations (removeTopDecorations d) ≡ ∅
timeDecorations∘remove≡[] {d} rewrite decorations∘remove≡[] {d} = refl

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

subterms⁺ = mkCollectList go
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

subtermsᵃ′ subtermsᵃ⁺ subtermsᵃ : Advertisement → List Contract
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
      where open ⊆-Reasoning Contract renaming (begin_ to begin⊆_; _∎ to _⊆∎)

    subterms⁺⊆ᵛ′ : subtermsᵛ⁺ vcs ⊆ subtermsᵛ′ vcs
    subterms⁺⊆ᵛ′ {[]} = id
    subterms⁺⊆ᵛ′ {(v , c) ∷ vcs} =
      begin⊆ subtermsᵛ⁺ ((v , c) ∷ vcs) ≡⟨⟩
            subtermsᶜ⁺ c ++ subtermsᵛ⁺ vcs ⊆⟨ {!!} ⟩
            subtermsᶜ′ c ++ subtermsᵛ′ vcs ≡⟨⟩
            subtermsᵛ′ ((v , c) ∷ vcs) ⊆∎
      where open ⊆-Reasoning Contract renaming (begin_ to begin⊆_; _∎ to _⊆∎)
-}

h-subᵈ :
  d ∈ subtermsᵈ′ d′
  ──────────────────────────────────────
  removeTopDecorations d ∈ subtermsᵈ⁺ d′

h-subᶜ :
  d ∈ subtermsᶜ′ ds
  ──────────────────────────────────────
  removeTopDecorations d ∈ subtermsᶜ⁺ ds

h-subᵛ :
  d ∈ subtermsᵛ′ vcs
  ───────────────────────────────────────
  removeTopDecorations d ∈ subtermsᵛ⁺ vcs

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

↦-∈ : ∀ {R : Contract → Set}
  → (∀ {d} → d ∈ ds → subterms⁺ (C d) L.↦′ R)
  → subterms⁺ (CS ds) L.↦′ R
↦-∈ {ds = c ∷ cs} f x∈
  with ∈-++⁻ (subterms⁺ (C c)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ (f ∘ there) x∈ʳ

↦-∈ᵛ : ∀ {R : Contract → Set}
  → (∀ {cs} → cs ∈ map proj₂ vcs → subterms⁺ (CS cs) L.↦′ R)
  → subterms⁺ (VCS vcs) L.↦′ R
↦-∈ᵛ {vcs = (_ , cs) ∷ vcs} f x∈
  with ∈-++⁻ (subterms⁺ (CS cs)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ᵛ (f ∘ there) x∈ʳ

mutual
  subterms⊆ᶜˢ : ds ⊆ subterms′ (CS ds)
  subterms⊆ᶜˢ {ds = d ∷ ds} (here refl) = here refl
  subterms⊆ᶜˢ {ds = d ∷ ds} (there d∈)  = there $ ∈-++⁺ʳ (subterms′ $ C d) (subterms⊆ᶜˢ d∈)

  subterms⊆ᵛᶜˢ : (v , ds) ∈ vcs → ds ⊆ subterms′ (VCS vcs)
  subterms⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} (here refl) = ∈-++⁺ˡ ∘ subterms⊆ᶜˢ
  subterms⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} (there p)   = ∈-++⁺ʳ (subterms′ (CS ds)) ∘ subterms⊆ᵛᶜˢ p

  subterms⊆ᵛᶜˢ′ : c ∈ map proj₂ vcs → subtermsᶜ′ c ⊆ subtermsᵈ′ (split vcs)
  subterms⊆ᵛᶜˢ′ {vcs = (v , cs) ∷ _}   (here refl) = ∈-++⁺ˡ
  subterms⊆ᵛᶜˢ′ {vcs = (v , cs) ∷ vcs} (there c∈)  = ∈-++⁺ʳ _ ∘ subterms⊆ᵛᶜˢ′ {vcs = vcs} c∈

  subterms⊆ᵛᶜⁱˢ : ∀ {vcis : List (Value × Contracts × Id)} → let (vs , cs , ys) = unzip₃ vcis in
      c ∈ cs
    → subtermsᶜ′ c ⊆ subtermsᵈ′ (split $ zip vs cs)
  subterms⊆ᵛᶜⁱˢ {vcis = (v , cs , _) ∷ _}    (here refl)
    = ∈-++⁺ˡ
  subterms⊆ᵛᶜⁱˢ {vcis = (v , cs , _) ∷ vcis} (there c∈)
    = ∈-++⁺ʳ _ ∘ subterms⊆ᵛᶜⁱˢ {vcis = vcis} c∈

mutual
  subterms′-names⊆ᶜ : d ∈ subterms′ (C d′) → names d ⊆ˢ names d′
  subterms′-names⊆ᶜ {d′ = d} with d
  ... | put xs &reveal as if p ⇒ ds = λ x∈
    → names-put≡ {xs = xs}{as}{p}{ds} .proj₂
    ∘ ∈-∪⁺ʳ _ (mapˢ inj₂ xs) (mapˢ inj₁ as ∪ names ds)
    ∘ ∈-∪⁺ʳ _ (mapˢ inj₁ as) (names ds)
    ∘ subterms′-names⊆ᶜˢ {ds = ds} x∈
  ... | withdraw _                  = λ ()
  ... | split vcs                   = subterms′-names⊆ᵛᶜˢ {vcs = vcs}
  ... | _ ⇒ d′                      = subterms′-names⊆ᶜ {d′ = d′}
  ... | after _ ⇒ d′                = subterms′-names⊆ᶜ {d′ = d′}

  subterms′-names⊆ᶜˢ : d ∈ subterms′ (CS ds) → names d ⊆ˢ names ds
  subterms′-names⊆ᶜˢ {ds = d ∷ ds} (here refl)
    = names≡ {d = d}{ds} .proj₂
    ∘ ∈-∪⁺ˡ _ (names d) (names ds)
  subterms′-names⊆ᶜˢ {ds = d ∷ ds} (there p)
    = names≡ {d = d}{ds} .proj₂
    ∘ (case ∈-++⁻ (subtermsᵈ′ d) p of λ where
        (inj₁ p) → ∈-∪⁺ˡ _ (names d) (names ds) ∘ subterms′-names⊆ᶜ {d′ = d} p
        (inj₂ p) → ∈-∪⁺ʳ _ (names d) (names ds) ∘ subterms′-names⊆ᶜˢ {ds = ds} p)

  subterms′-names⊆ᵛᶜˢ : d ∈ subterms′ (VCS vcs) → names d ⊆ˢ names vcs
  subterms′-names⊆ᵛᶜˢ {vcs = (v , ds) ∷ vcs} p
    = names≡ᵛ {v = v}{ds}{vcs} .proj₂
    ∘ (case ∈-++⁻ (subtermsᶜ′ ds) p of λ where
        (inj₁ p) → ∈-∪⁺ˡ _ (names ds) (names vcs) ∘ subterms′-names⊆ᶜˢ {ds = ds} p
        (inj₂ p) → ∈-∪⁺ʳ _ (names ds) (names vcs) ∘ subterms′-names⊆ᵛᶜˢ {vcs = vcs} p)

mutual
  subterms′-putComponents⊆ᶜ : d ∈ subterms′ (C d′) → putComponents d ⊆ˢ putComponents d′
  subterms′-putComponents⊆ᶜ {d′ = d} with d
  ... | put xs &reveal as if p ⇒ ds = λ x∈
    → putComponents-put≡ {xs = xs}{as}{p}{ds} .proj₂
    ∘ thereˢ {xs = putComponents ds}
    ∘ subterms′-putComponents⊆ᶜˢ {ds = ds} x∈
  ... | withdraw _                = λ ()
  ... | split vcs                 = subterms′-putComponents⊆ᵛᶜˢ {vcs = vcs}
  ... | _ ⇒ d′                    = subterms′-putComponents⊆ᶜ {d′ = d′}
  ... | after _ ⇒ d′              = subterms′-putComponents⊆ᶜ {d′ = d′}

  subterms′-putComponents⊆ᶜˢ : d ∈ subterms′ (CS ds) → putComponents d ⊆ˢ putComponents ds
  subterms′-putComponents⊆ᶜˢ {ds = d ∷ ds}  (here refl)
    = putComponents≡ {d = d}{ds} .proj₂
    ∘ ∈-∪⁺ˡ _ (putComponents d) (putComponents ds)
  subterms′-putComponents⊆ᶜˢ {ds = d ∷ ds} (there p)
    = putComponents≡ {d = d}{ds} .proj₂
    ∘ (case ∈-++⁻ (subterms′ $ C d) p of λ where
        (inj₁ p′) → ∈-∪⁺ˡ _ (putComponents d) (putComponents ds)
                  ∘ subterms′-putComponents⊆ᶜ {d′ = d} p′
        (inj₂ p′) → ∈-∪⁺ʳ _ (putComponents d) (putComponents ds)
                  ∘ subterms′-putComponents⊆ᶜˢ {ds = ds} p′)

  subterms′-putComponents⊆ᵛᶜˢ : d ∈ subterms′ (VCS vcs) → putComponents d ⊆ˢ putComponents vcs
  subterms′-putComponents⊆ᵛᶜˢ {vcs = (v , ds) ∷ vcs} p
    = putComponents≡ᵛ {v = v}{ds}{vcs} .proj₂
    ∘ (case ∈-++⁻ (subterms′ (CS ds)) p of λ where
        (inj₁ p′) → ∈-∪⁺ˡ _ (putComponents ds) (putComponents vcs) ∘ subterms′-putComponents⊆ᶜˢ {ds = ds} p′
        (inj₂ p′) → ∈-∪⁺ʳ _ (putComponents ds) (putComponents vcs) ∘ subterms′-putComponents⊆ᵛᶜˢ {vcs = vcs} p′)

mutual
  subterms′-part⊆ᶜ : d ∈ subtermsᵈ′ d′ → participants d ⊆ˢ participants d′
  subterms′-part⊆ᶜ {d′ = d} with d
  ... | put _ &reveal _ if _ ⇒ ds = subterms′-part⊆ᶜˢ {ds = ds}
  ... | withdraw _                = λ ()
  ... | split vcs                 = subterms′-part⊆ᵛᶜˢ {vcs = vcs}
  ... | A ⇒ d′                    = λ x∈
    → participants-auth≡ {A = A}{d′} .proj₂
    ∘ thereˢ {xs = participants d′}
    ∘ subterms′-part⊆ᶜ {d′ = d′} x∈
  ... | after _ ⇒ d′              = subterms′-part⊆ᶜ {d′ = d′}

  subterms′-part⊆ᶜˢ : d ∈ subtermsᶜ′ ds → participants d ⊆ˢ participants ds
  subterms′-part⊆ᶜˢ {ds = d ∷ ds} (here refl)
    = participants≡ {d = d}{ds} .proj₂
    ∘ ∈-∪⁺ˡ _ (participants d) (participants ds)
  subterms′-part⊆ᶜˢ {ds = d ∷ ds} (there p)
    = participants≡ {d = d}{ds} .proj₂
    ∘ (case ∈-++⁻ (subterms′ $ C d) p of λ where
        (inj₁ p′) → ∈-∪⁺ˡ _ (participants d) (participants ds)
                  ∘ subterms′-part⊆ᶜ {d′ = d} p′
        (inj₂ p′) → ∈-∪⁺ʳ _ (participants d) (participants ds)
                  ∘ subterms′-part⊆ᶜˢ {ds = ds} p′)

  subterms′-part⊆ᵛᶜˢ : d ∈ subtermsᵛ′ vcs → participants d ⊆ˢ participants vcs
  subterms′-part⊆ᵛᶜˢ {vcs = (v , ds) ∷ vcs} p
    = participants≡ᵛ {v = v}{ds}{vcs} .proj₂
    ∘ (case ∈-++⁻ (subterms′ (CS ds)) p of λ where
        (inj₁ p′) → ∈-∪⁺ˡ _ (participants ds) (participants vcs) ∘ subterms′-part⊆ᶜˢ {ds = ds} p′
        (inj₂ p′) → ∈-∪⁺ʳ _ (participants ds) (participants vcs) ∘ subterms′-part⊆ᵛᶜˢ {vcs = vcs} p′)
