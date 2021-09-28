------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Prelude.Decidable
open import Prelude.General
open import Prelude.Setoid
open import Prelude.Traces
open import Prelude.Bifunctor
open import Prelude.Coercions

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest

instance
  IS-Cfg : ISetoid Cfg
  IS-Cfg ._≈_ = _↭_ on to[ Cfg′ ]

  IS-TCfg : ISetoid Cfgᵗ
  IS-TCfg ._≈_ (Γ at t) (Γ′ at t′) = (t ≡ t′) × (Γ ≈ Γ′)

  -- ** Initiality (for constructing traces)
  HI-Cfg : HasInitial Cfg
  HI-Cfg .Initial = λ where
    (⟨ _ has _ ⟩at _) → ⊤
    (l ∣ r)           → Initial l × Initial r
    _                 → ⊥

  HI-TCfg : HasInitial Cfgᵗ
  HI-TCfg .Initial (Γ at t) = Initial Γ × (t ≡ 0)

cfgToList : Cfg → List Cfg
cfgToList = map to[ Cfg ] ∘ to[ Cfg′ ]

cfgToList-++ : ∀ l r → cfgToList (l ∣ r) ≡ cfgToList l ++ cfgToList r
cfgToList-++ l r = L.map-++-commute to[ Cfg ] (to[ Cfg′ ] l) (to[ Cfg′ ] r)

∈ᶜ-++⁻ : ∀ l r → Γ₀ ∈ cfgToList (l ∣ r) → Γ₀ ∈ cfgToList l ⊎ Γ₀ ∈ cfgToList r
∈ᶜ-++⁻ l r rewrite cfgToList-++ l r = L.Mem.∈-++⁻ (cfgToList l)

∈ᶜ-++⁺ˡ : ∀ l r → Γ₀ ∈ cfgToList l → Γ₀ ∈ cfgToList (l ∣ r)
∈ᶜ-++⁺ˡ l r rewrite cfgToList-++ l r = L.Mem.∈-++⁺ˡ

∈ᶜ-++⁺ʳ : ∀ l r → Γ₀ ∈ cfgToList r → Γ₀ ∈ cfgToList (l ∣ r)
∈ᶜ-++⁺ʳ l r rewrite cfgToList-++ l r = L.Mem.∈-++⁺ʳ (cfgToList l)

infix 4 _∈ᶜ_ _∉ᶜ_
_∈ᶜ_ _∉ᶜ_ : Rel₀ Cfg
c ∈ᶜ c′ = c ∈ cfgToList c′
c ∉ᶜ c′ = ¬ c ∈ᶜ c′

_≢deposit : Cfg → Set
_≢deposit = λ where
  (⟨ _ has _ ⟩at _) → ⊥
  _                 → ⊤

Initial⇒∉ : ⦃ Γ₀ ≢deposit ⦄ → Initial Γ → Γ₀ ∉ᶜ Γ
Initial⇒∉ {Γ = ⟨ _ has _ ⟩at _} ⦃ () ⦄ _ (here refl)
Initial⇒∉ {Γ = l ∣ r} ⦃ ≢dep ⦄ (pˡ , pʳ) =
  ∈ᶜ-++⁻ l r >≡>
  Sum.[ Initial⇒∉ ⦃ ≢dep ⦄ pˡ
      , Initial⇒∉ ⦃ ≢dep ⦄ pʳ ]

∈ᶜ-resp-≈ : Γ ≈ Γ′ → Γ₀ ∈ᶜ Γ → Γ₀ ∈ᶜ Γ′
∈ᶜ-resp-≈ {Γ}{Γ′}{Γ₀} Γ≈Γ′ c∈
  with Γ¹ , Γ¹∈ , Γ₀≡ ← L.Mem.∈-map⁻ to[ Cfg ] c∈
  with Γ¹∈′ ← L.Perm.∈-resp-↭ Γ≈Γ′ Γ¹∈
  = ⟪ _∈ cfgToList Γ′ ⟫ Γ₀≡ ~: L.Mem.∈-map⁺ to[ Cfg ] Γ¹∈′

∉ᶜ-resp-≈ : Γ ≈ Γ′ → Γ₀ ∉ᶜ Γ → Γ₀ ∉ᶜ Γ′
∉ᶜ-resp-≈ {Γ}{Γ′}{Γ₀} Γ≈ c∉ = c∉ ∘ ∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈)

∉ᶜ-|| : ∀ {A : Set} {f : A → Cfg}
  → (∀ {x} → Γ ∉ᶜ f x)
    --———————————————————————————
  → ∀ xs → Γ ∉ᶜ || map f xs
∉ᶜ-|| Γ≢ [] ()
∉ᶜ-|| Γ∉ (_ ∷ []) Γ∈ = Γ∉ Γ∈
∉ᶜ-|| {f = f} Γ≢ (x ∷ xs@(_ ∷ _)) =
  ∈ᶜ-++⁻ (f x) (|| map f xs) >≡>
  Sum.[ Γ≢
      , ∉ᶜ-|| Γ≢ xs ]

private variable X Y : Set

collectFromBase : (BaseCfg → List X) → (Cfg → List X)
collectFromBase f = collectFromList f ∘ to[ Cfg′ ]

collectFromBase-++ : ⦃ I : BaseCfg has X ⦄ → ∀ l r → let f = collectFromBase (collect ⦃ I ⦄) in
    f (l ∣ r) ≡ f l ++ f r
collectFromBase-++ l r rewrite cfgToList-++ l r | concatMap-++ collect (to[ Cfg′ ] l) (to[ Cfg′ ] r) = refl

mapMaybe∘collectFromBase-++ : ∀ ⦃ I : BaseCfg has X ⦄ (g : X → Maybe Y) l r → let f = collectFromBase (collect ⦃ I ⦄) in
    mapMaybe g (f (l ∣ r)) ≡ mapMaybe g (f l) ++ mapMaybe g (f r)
mapMaybe∘collectFromBase-++ ⦃ I ⦄ g l r = begin
    mapMaybe g (f $ l ∣ r)
  ≡⟨ cong (mapMaybe g) (collectFromBase-++ l r) ⟩
    mapMaybe g (f l ++ f r)
  ≡⟨ mapMaybe-++ g (f l) (f r) ⟩
    mapMaybe g (f l) ++ mapMaybe g (f r)
  ∎ where open ≡-Reasoning
          f = collectFromBase (collect ⦃ I ⦄)

∈-collect-++⁻ : ∀ l r {x : X} → ⦃ I : BaseCfg has X ⦄ → let f = collectFromBase (collect ⦃ I ⦄) in
    x ∈ f (l ∣ r) → x ∈ f l ⊎ x ∈ f r
∈-collect-++⁻ {X = X} l r rewrite collectFromBase-++ {X = X} l r = L.Mem.∈-++⁻ _

∈-collect-++⁺ˡ : ∀ l r {x : X} → ⦃ I : BaseCfg has X ⦄ → let f = collectFromBase (collect ⦃ I ⦄) in
    x ∈ f l → x ∈ f (l ∣ r)
∈-collect-++⁺ˡ {X = X} l r rewrite collectFromBase-++ {X = X} l r = L.Mem.∈-++⁺ˡ

∈-collect-++⁺ʳ : ∀ l r {x : X} → ⦃ I : BaseCfg has X ⦄ → let f = collectFromBase (collect ⦃ I ⦄) in
    x ∈ f r → x ∈ f (l ∣ r)
∈-collect-++⁺ʳ {X = X} l r rewrite collectFromBase-++ {X = X} l r = L.Mem.∈-++⁺ʳ _

instance
  HNᵃᶜ : Action has Name
  HNᵃᶜ .collect ac with ac
  ... | ♯▷ ad            = collect ad
  ... | x ▷ˢ ad          = inj₁ x ∷ collect ad
  ... | x ▷ c            = inj₁ x ∷ collect c
  ... | x ↔ y ▷⟨ _ , _ ⟩ = map inj₁ ⟦ x , y ⟧
  ... | x ▷⟨ _ , _ , _ ⟩ = [ inj₁ x ]
  ... | x ▷ᵈ _           = [ inj₁ x ]
  ... | xs , _ ▷ᵈˢ x     = map inj₁ (x ∷ xs)

  HBC⇒HC : ⦃ BaseCfg has X ⦄ → Cfg has X
  HBC⇒HC .collect = collectFromBase (collect ⦃ it ⦄)

  HDᶜᶠ : BaseCfg has DepositRef
  HDᶜᶠ .collect = λ where
    (`⟨ A has v ⟩at x) → [ A , v , x ]
    _                  → []

  HNᶜᶠ : BaseCfg has Name
  HNᶜᶠ .collect = λ where
    -- secrets
    (`⟨ _ ∶ s ♯ _ ⟩)   → [ inj₁ s ]
    (_ `∶ s ♯ _)       → [ inj₁ s ]
    -- names
    (`⟨ _ ,   _ ⟩at x) → [ inj₂ x ]
    (`⟨ _ has _ ⟩at x) → [ inj₂ x ]
    _                  → []

  HAᶜᶠ : BaseCfg has Action
  HAᶜᶠ .collect = λ where
    (_ `auth[ a ]) → [ a ]
    _              → []

  -- ** See `authorizedHonAds` below
  HAᵇᶜᶠ : BaseCfg has Advertisement
  HAᵇᶜᶠ .collect = λ where
    (A `auth[ ♯▷ ad ]) → if does (A ∈? Hon) then [ ad ] else []
    _                  → []

  Hᶜᶠ⇒Hᵗᶜᶠ : ⦃ Cfg has X ⦄ → Cfgᵗ has X
  Hᶜᶠ⇒Hᵗᶜᶠ ⦃ hx ⦄ .collect = collect ⦃ hx ⦄ ∘ cfg

authorizedActions : ⦃ _ :  X has Action ⦄ → X → List Action
authorizedActions = collect

advertisements : ⦃ _ :  X has Advertisement ⦄ → X → List Advertisement
advertisements = collect
authorizedHonAds = advertisements

-- authorizedAds : ⦃ _ :  X has Action ⦄ → X → List Advertisement
-- authorizedAds = mapMaybe (λ where (♯▷ ad) → just ad; _ → nothing)
--               ∘ authorizedActions

secretsOfᶜᶠ : Participant → Cfg → Secrets
secretsOfᶜᶠ A = {- Set'.nub ∘-} go
  where
    go : Cfg → Secrets
    go (⟨ B ∶ a ♯ _ ⟩) = if A == B then [ a ] else []
    go (l ∣ r)         = go l ++ go r
    go _               = []

committedParticipants : Advertisement → Cfg → List Participant
committedParticipants ad = collect
  module ∣committedParticipants∣ where
    instance
      go : BaseCfg has Participant
      go .collect = λ where
        (p `auth[ (♯▷ ad′) ]) → if ad == ad′ then [ p ] else []
        _                     → []

committed⇒authCommit :
   A ∈ committedParticipants ad Γ
   --—————————————————————————————
 → A auth[ ♯▷ ad ] ∈ᶜ Γ
committed⇒authCommit {ad = ad} {Γ = _ auth[ ♯▷ ad′ ]} A∈
  with ad ≟ ad′ | A∈
... | yes refl | here refl = here refl
committed⇒authCommit {A}{ad} {Γ = l ∣ r} A∈
  with ∈-collect-++⁻ l r ⦃ ∣committedParticipants∣.go ad ⦄ A∈
... | inj₁ A∈ˡ = ∈ᶜ-++⁺ˡ l r (committed⇒authCommit {Γ = l} A∈ˡ)
... | inj₂ A∈ʳ = ∈ᶜ-++⁺ʳ l r (committed⇒authCommit {Γ = r} A∈ʳ)

module _ (A∈ : A ∈ Hon) where
  committed⇒authAd :
      A ∈ committedParticipants ad Γ
    → ad ∈ authorizedHonAds Γ
  -- committed⇒authAd {Γ} {ad} P
  committed⇒authAd {ad} {p auth[ ♯▷ ad′ ]} P
    with ad ≟ ad′ | P
  ... | no _    | ()
  ... | yes ad≡ | here refl
    rewrite dec-true (A ∈? Hon) A∈
    = here ad≡
  committed⇒authAd {ad} {l ∣ r} P
    with ∈-collect-++⁻ l r ⦃ ∣committedParticipants∣.go ad ⦄  P
  ... | inj₁ ∈l = ∈-collect-++⁺ˡ l r (committed⇒authAd {Γ = l} ∈l)
  ... | inj₂ ∈r = ∈-collect-++⁺ʳ l r (committed⇒authAd {Γ = r} ∈r)

committedSingle≡ : committedParticipants ad (A auth[ ♯▷ ad ]) ≡ [ A ]
committedSingle≡ {ad} rewrite ≟-refl _≟_ ad = refl

committedPartG≡ : ∀ ps → committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps) ≡ ps
committedPartG≡ [] = refl
committedPartG≡ (_ ∷ []) = committedSingle≡
committedPartG≡ {ad} (p ∷ ps@(_ ∷ _)) =
  begin
    committedParticipants ad (|| (p auth[ ♯▷ ad ] ∷ map (_auth[ ♯▷ ad ]) ps))
  ≡⟨⟩
    committedParticipants ad (|| (p auth[ ♯▷ ad ] ∷ map (_auth[ ♯▷ ad ]) ps))
  ≡⟨ collectFromBase-++ ⦃ ∣committedParticipants∣.go ad ⦄ (p auth[ ♯▷ ad ]) (|| map (_auth[ ♯▷ ad ]) ps) ⟩
    committedParticipants ad (p auth[ ♯▷ ad ]) ++ committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)
  ≡⟨ cong (_++ committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)) committedSingle≡ ⟩
    p ∷ committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)
  ≡⟨ cong (p ∷_) (committedPartG≡ ps) ⟩
    p ∷ ps
  ∎ where open ≡-Reasoning

-- ** Collections of equivalent configurations.

-- ≈⇒names↭ : _≈_ {A = Cfg} ⇒² _↭⦅ names ⦆_
≈⇒names↭ : Γ ≈ Γ′ → Γ ↭⦅ names ⦆ Γ′
≈⇒names↭ = collectFromList↭ (collect ⦃ it ⦄)

≈⇒ads↭   : Γ ≈ Γ′ → Γ ↭⦅ advertisements ⦆ Γ′
≈⇒ads↭ = collectFromList↭ (collect ⦃ it ⦄)

≈⇒namesʳ↭ : Γ ≈ Γ′ → Γ ↭⦅ namesʳ ⦆ Γ′
≈⇒namesʳ↭ {Γ}{Γ′} eq = mapMaybe-↭ isInj₂ $ ≈⇒names↭ {Γ}{Γ′} eq

≈⇒namesˡ↭ : Γ ≈ Γ′ → Γ ↭⦅ namesˡ ⦆ Γ′
≈⇒namesˡ↭ {Γ}{Γ′} eq = mapMaybe-↭ isInj₁ $ ≈⇒names↭ {Γ}{Γ′} eq

∈-resp-≈ : ∀ {Z Z′ A : Set} → ⦃ _ : A has Z ⦄ → ⦃ _ : ISetoid A ⦄
  → (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′)
  → (∀ {a a′ : A} → a ≈ a′ → a ↭⦅ f ⦆ a′)
  → ∀ (z : Z′) → (λ ◆ → z ∈ f ◆) Respects _≈_
∈-resp-≈ _ ≈⇒↭ x = L.Perm.∈-resp-↭ ∘ ≈⇒↭

∈ads-resp-≈    = ∈-resp-≈ advertisements (λ {Γ}{Γ′} → ≈⇒ads↭    {Γ}{Γ′})
∈names-resp-≈  = ∈-resp-≈ names          (λ {Γ}{Γ′} → ≈⇒names↭  {Γ}{Γ′})
∈namesˡ-resp-≈ = ∈-resp-≈ namesˡ         (λ {Γ}{Γ′} → ≈⇒namesˡ↭ {Γ}{Γ′})
∈namesʳ-resp-≈ = ∈-resp-≈ namesʳ         (λ {Γ}{Γ′} → ≈⇒namesʳ↭ {Γ}{Γ′})

--- ** name helpers

deposit∈Γ⇒namesʳ : ∀ {Γ}
  → ⟨ A has v ⟩at x ∈ᶜ Γ
  → x ∈ namesʳ Γ
deposit∈Γ⇒namesʳ {A} {v} {x} {` _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ , _ ⟩at _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ has _ ⟩at .x} (here refl) = here refl
deposit∈Γ⇒namesʳ {A} {v} {x} {_ auth[ _ ]} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ ∶ _ ♯ _ ⟩} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {_ ∶ _ ♯ _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {l ∣ r} d∈
  with ∈ᶜ-++⁻ l r d∈
... | inj₁ d∈ˡ = let _ , x∈ , d≡ = ∈-mapMaybe⁻ isInj₂ (deposit∈Γ⇒namesʳ {Γ = l} d∈ˡ)
                 in ∈-mapMaybe⁺ isInj₂ (∈-collect-++⁺ˡ l r x∈) d≡
... | inj₂ d∈ʳ = let _ , x∈ , d≡ = ∈-mapMaybe⁻ isInj₂ (deposit∈Γ⇒namesʳ {Γ = r} d∈ʳ)
                 in ∈-mapMaybe⁺ isInj₂ (∈-collect-++⁺ʳ l r x∈) d≡

namesʳ-∥map-authDestroy : ∀ (ds : List (Participant × Value × Id))
  → map (proj₂ ∘ proj₂) ds ⊆ namesʳ (|| map (uncurry₃ ⟨_has_⟩at_) ds)
namesʳ-∥map-authDestroy (_ ∷ []) (here refl) = here refl
namesʳ-∥map-authDestroy (_ ∷ _ ∷ _) (here refl) = here refl
namesʳ-∥map-authDestroy ((Bᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) (there d∈) = there $ (namesʳ-∥map-authDestroy ds) d∈

private
  n≡ : ∀ {A : Set} {P Q : A → Cfg}
    → (∀ x → Null $ namesʳ (Q x) )
    → (xs : List A)
    → namesʳ (|| map (λ x → P x ∣ Q x) xs)
    ≡ namesʳ (|| map P xs)
  n≡ ∀x [] = refl
  n≡ {P = P}{Q} ∀x (x₁ ∷ []) = P∣Q≡
    where
      P∣Q≡ : namesʳ (P x₁ ∣ Q x₁) ≡ namesʳ (P x₁)
      P∣Q≡ rewrite mapMaybe∘collectFromBase-++ isInj₂ (P x₁) (Q x₁)
                | ∀x x₁
                | L.++-identityʳ (namesʳ $ P x₁)
                = refl
  n≡ {P = P}{Q} ∀x (x₁ ∷ xs@(_ ∷ _)) =
    begin
      namesʳ (|| (P x₁ ∣ Q x₁ ∷ map (λ x → P x ∣ Q x) xs))
    ≡⟨⟩
      namesʳ (P x₁ ∣ Q x₁ ∣ || map (λ x → P x ∣ Q x) xs)
    ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (P x₁ ∣ Q x₁) (|| map (λ x → P x ∣ Q x) xs) ⟩
      namesʳ (P x₁ ∣ Q x₁) ++ namesʳ (|| map (λ x → P x ∣ Q x) xs)
    ≡⟨ cong (_++ namesʳ (|| map (λ x → P x ∣ Q x) xs)) P∣Q≡ ⟩
      namesʳ (P x₁) ++ namesʳ (|| map (λ x → P x ∣ Q x) xs)
    ≡⟨ cong (namesʳ (P x₁) ++_) rec ⟩
      namesʳ (P x₁) ++ namesʳ (|| map P xs)
    ≡⟨ sym $ mapMaybe∘collectFromBase-++ isInj₂ (P x₁) (|| map P xs) ⟩
      namesʳ (|| (P x₁ ∷ map P xs))
    ∎
    where
      open ≡-Reasoning

      P∣Q≡ : namesʳ (P x₁ ∣ Q x₁) ≡ namesʳ (P x₁)
      P∣Q≡ rewrite collectFromBase-++ {X = Name} (P x₁) (Q x₁)
                | mapMaybe-++ isInj₂ (names $ P x₁) (names $ Q x₁)
                | ∀x x₁
                | L.++-identityʳ (namesʳ $ P x₁)
                = refl

      rec : namesʳ (|| map (λ x → P x ∣ Q x) xs) ≡ namesʳ (|| map P xs)
      rec = n≡ {P = P}{Q} ∀x xs

namesʳ-∥map-destroy : ∀ (ds : List (Participant × Value × Id)) → let xs = map (proj₂ ∘ proj₂) ds in
  xs ⊆ namesʳ (|| map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds))
namesʳ-∥map-destroy {y = y} ds {x} x∈ = qed
  where
    PVI = Participant × Value × Id
    x̂ = map (proj₂ ∘ proj₂) ds
    eds = enumerate ds

    P : PVI → Cfg
    P (Aᵢ , vᵢ , xᵢ) = ⟨ Aᵢ has vᵢ ⟩at xᵢ

    P′ : ∀ {A : Set} → A × PVI → Cfg
    P′ = P ∘ proj₂

    Q P∣Q : Index ds × PVI → Cfg
    Q (i , Aᵢ , vᵢ , xᵢ) = Aᵢ auth[ x̂ , ‼-map {xs = ds} i ▷ᵈˢ y ]
    P∣Q x = P′ x ∣ Q x

    h : namesʳ (|| map P∣Q eds)
      ≡ namesʳ (|| map P′ eds)
    h = n≡ {A = Index ds × PVI} {P = P′} {Q = Q} (λ _ → refl) eds

    -- [BUG] if I replace `enumerate ds` with `eds` I get an error!?
    h′ : ∀ (ds : List PVI) → map P′ (enumerate ds) ≡ map P ds
    h′ [] = refl
    h′ (pvi ∷ ds) = cong (_ ∷_) qed
      where
        rec : map P′ (zip (L.tabulate {n = length ds} (fsuc ∘ id)) ds)
            ≡ map (P′ ∘ map₁ fsuc) (zip (L.tabulate {n = length ds} id) ds)
        rec = map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate {m = length ds} ds {P = P′} {f = id}

        qed : map P′ (zip (L.tabulate {n = length ds} fsuc) ds)
            ≡ map P ds
        qed = trans rec (h′ ds)

    qed : x ∈ namesʳ (|| map P∣Q eds)
    qed rewrite h | h′ ds = namesʳ-∥map-authDestroy ds x∈

namesʳ-∥map-authCommit : ∀ {secrets : List (Secret × Maybe ℕ)} → let (as , ms) = unzip secrets in
    as ⊆ namesˡ (|| map (uncurry ⟨ A ∶_♯_⟩) secrets)
namesʳ-∥map-authCommit {secrets = `∅ᶜ} ()
namesʳ-∥map-authCommit {secrets = (_ , _) ∷ []} (here refl) = here refl
namesʳ-∥map-authCommit {secrets = (_ , _) ∷ ss@(_ ∷ _)} (here refl) = here refl
namesʳ-∥map-authCommit {secrets = _ ∷ ss@(_ ∷ _)} (there a∈) = there (namesʳ-∥map-authCommit {secrets = ss} a∈)
