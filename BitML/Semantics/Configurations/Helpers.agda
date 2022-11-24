------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------
open import Prelude.Init
open L.Mem hiding (_∈_)
open L.Perm using (∈-resp-↭; map⁺)
open import Prelude.Lists.PermutationsMeta
open import Prelude.Lists.SetEquality
open import Prelude.Lists.Irrelevance
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.SetCollections
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Prelude.Decidable
open import Prelude.General
open import Prelude.Setoid
open import Prelude.Traces
open import Prelude.Bifunctor
open import Prelude.Irrelevance
open import Prelude.Coercions
open import Prelude.Split renaming (split to mkSplit)
open import Prelude.Null
open import Prelude.Sets hiding (_⊣_)
open import Prelude.FromList
open import Prelude.ToList

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
  Setoid-Cfg′ : ISetoid Cfg′
  Setoid-Cfg′ = λ where
    .relℓ → 0ℓ
    ._≈_ → _↭_

  SetoidLaws-Cfg′ : Setoid-Laws Cfg′
  SetoidLaws-Cfg′ .isEquivalence = record {IsEquivalence L.Perm.↭-isEquivalence}

  Setoid-Cfg : ISetoid Cfg
  Setoid-Cfg = λ where
    .relℓ → 0ℓ
    ._≈_ → _≈_ on to[ Cfg′ ]

  SetoidLaws-Cfg : Setoid-Laws Cfg
  SetoidLaws-Cfg .isEquivalence = record {IsEquivalence L.Perm.↭-isEquivalence}

  Setoid-Cfgᵗ : ISetoid Cfgᵗ
  Setoid-Cfgᵗ = λ where
    .relℓ → 0ℓ
    ._≈_ (Γ at t) (Γ′ at t′) → (t ≡ t′) × (Γ ≈ Γ′)

  SetoidLaws-Cfgᵗ : Setoid-Laws Cfgᵗ
  SetoidLaws-Cfgᵗ .isEquivalence = record
    { refl  = refl , ↭-refl
    ; sym   = λ where (t≡ , Γ≈) → sym t≡ , ↭-sym Γ≈
    ; trans = λ where (t≡ , Γ≈) (≡t , ≈Γ) → trans t≡ ≡t , ↭-trans Γ≈ ≈Γ
    }

  -- ** Initiality (for constructing traces)
  Initial-Cfg : HasInitial Cfg
  Initial-Cfg .Initial = λ where
    ∅ᶜ                → ⊤
    (⟨ _ has _ ⟩at _) → ⊤
    (l ∣ r)           → Initial l × Initial r
    _                 → ⊥

  Initial-Cfgᵗ : HasInitial Cfgᵗ
  Initial-Cfgᵗ .Initial (Γ at t) = Initial Γ × (t ≡ 0)

≈ᵗ-refl : Γₜ ≈ Γₜ
≈ᵗ-refl = refl , ↭-refl

-- T0D0: find general scheme
-- ∙ list-like things + map-commuting ~> membership lemmas
cfgToList : Cfg → List Cfg
cfgToList = map to[ Cfg ] ∘ to[ Cfg′ ]

cfgToList-++ : ∀ l r → cfgToList (l ∣ r) ≡ cfgToList l ++ cfgToList r
cfgToList-++ l r = L.map-++-commute to[ Cfg ] (to[ Cfg′ ] l) (to[ Cfg′ ] r)

{-
cfgToList-++² : ∀ l c r → cfgToList (l ∣ c ∣ r) ≡ cfgToList l ++ cfgToList c ++ cfgToList r
cfgToList-++² l c r
  rewrite cfgToList-++ (l ∣ c) r | cfgToList-++ l c
        = L.++-assoc (cfgToList l) (cfgToList c) (cfgToList r)

cfgToList-++²′ : ∀ l c r → cfgToList (l ∣ (c ∣ r)) ≡ cfgToList l ++ cfgToList c ++ cfgToList r
cfgToList-++²′ l c r
  rewrite cfgToList-++ l (c ∣ r) | cfgToList-++ c r
        = refl
-}

cfgToList-assoc : ∀ l c r → cfgToList (l ∣ c ∣ r) ≡ cfgToList (l ∣ (c ∣ r))
cfgToList-assoc l c r
  rewrite cfgToList-++ (l ∣ c) r | cfgToList-++ l c
        | cfgToList-++ l (c ∣ r) | cfgToList-++ c r
        = L.++-assoc (cfgToList l) (cfgToList c) (cfgToList r)

toCfg-injective : Injective≡ {A = BaseCfg} to[ Cfg ]
toCfg-injective {x = `` _}             {`` _}             refl = refl
toCfg-injective {x = `⟨ _ , _ ⟩at _}   {`⟨ _ , _ ⟩at _}   refl = refl
toCfg-injective {x = `⟨ _ has _ ⟩at _} {`⟨ _ has _ ⟩at _} refl = refl
toCfg-injective {x = _ `auth[ _ ]}     {_ `auth[ _ ]}     refl = refl
toCfg-injective {x = `⟨ _ ∶ _ ♯ _ ⟩}   {`⟨ _ ∶ _ ♯ _ ⟩}   refl = refl
toCfg-injective {x = _ `∶ _ ♯ _}       {_ `∶ _ ♯ _}       refl = refl

toCfg′-assoc : ∀ l c r → to[ Cfg′ ] (l ∣ c ∣ r) ≡ to[ Cfg′ ] (l ∣ (c ∣ r))
toCfg′-assoc l c r = L.map-injective toCfg-injective (cfgToList-assoc l c r)

≈ᶜ-assoc : ∀ l c r → l ∣ (c ∣ r) ≈ l ∣ c ∣ r
≈ᶜ-assoc l c r = ≈-reflexive (sym $ toCfg′-assoc l c r)

infix 4 _∈ᶜ_ _∉ᶜ_
_∈ᶜ_ _∉ᶜ_ : Rel₀ Cfg
c ∈ᶜ c′ = c ∈ cfgToList c′
c ∉ᶜ c′ = ¬ c ∈ᶜ c′

∈ᶜ-∪⁻ : ∀ l r → Γ₀ ∈ᶜ (l ∣ r) → Γ₀ ∈ᶜ l ⊎ Γ₀ ∈ᶜ r
∈ᶜ-∪⁻ l r rewrite cfgToList-++ l r = ∈-++⁻ (cfgToList l)

∈ᶜ-∪⁺ˡ : ∀ l r → Γ₀ ∈ᶜ l → Γ₀ ∈ᶜ (l ∣ r)
∈ᶜ-∪⁺ˡ l r rewrite cfgToList-++ l r = ∈-++⁺ˡ

∈ᶜ-∪⁺ʳ : ∀ l r → Γ₀ ∈ᶜ r → Γ₀ ∈ᶜ (l ∣ r)
∈ᶜ-∪⁺ʳ l r rewrite cfgToList-++ l r = ∈-++⁺ʳ (cfgToList l)

destruct-∈ᶜ-∪ : ∀ Γ Γ′ {x}
  → (x∈ : x ∈ᶜ (Γ ∣ Γ′))
    --——————————————————
  → (∃ λ (x∈ˡ : x ∈ᶜ Γ)  → x∈ ≡ ∈ᶜ-∪⁺ˡ Γ Γ′ x∈ˡ)
  ⊎ (∃ λ (x∈ʳ : x ∈ᶜ Γ′) → x∈ ≡ ∈ᶜ-∪⁺ʳ Γ Γ′ x∈ʳ)
destruct-∈ᶜ-∪ Γ Γ′ x∈ rewrite cfgToList-++ Γ Γ′ = destruct-∈-++ x∈

-- destruct-∈ᶜ-∪² : ∀ Γ Γ′ Γ″ {x}
--   → (x∈ : x ∈ᶜ (Γ ∣ Γ′ ∣ Γ″))
--     --————————————————————————————————————
--   → (∃ λ (x∈Γ  : x ∈ᶜ Γ)  → x∈ ≡ (∈ᶜ-∪⁺ˡ (Γ ∣ Γ′) Γ″ $ ∈ᶜ-∪⁺ˡ Γ Γ′ x∈Γ))
--   ⊎ (∃ λ (x∈Γ′ : x ∈ᶜ Γ′) → x∈ ≡ (∈ᶜ-∪⁺ˡ (Γ ∣ Γ′) Γ″ $ ∈ᶜ-∪⁺ʳ Γ Γ′ x∈Γ′))
--   ⊎ (∃ λ (x∈Γ″ : x ∈ᶜ Γ″) → x∈ ≡ (∈ᶜ-∪⁺ʳ (Γ ∣ Γ′) Γ″ x∈Γ″))

infix 4 _⊆ᶜ_ _⊈ᶜ_
_⊆ᶜ_ _⊈ᶜ_ : Rel₀ Cfg
c ⊆ᶜ c′ = cfgToList c ⊆ cfgToList c′
c ⊈ᶜ c′ = ¬ c ⊆ᶜ c′

⊆ᶜ-refl : Reflexive _⊆ᶜ_
⊆ᶜ-refl = id

⊆ᶜ-trans : Transitive _⊆ᶜ_
⊆ᶜ-trans Γ⊆ Γ⊆′ = Γ⊆′ ∘ Γ⊆

⊆ᶜ-∪⁺ˡ : ∀ l r → Δ ⊆ᶜ l → Δ ⊆ᶜ l ∣ r
⊆ᶜ-∪⁺ˡ l r = ∈ᶜ-∪⁺ˡ l r ∘_

⊆ᶜ-∪⁺ʳ : ∀ l r → Δ ⊆ᶜ r → Δ ⊆ᶜ l ∣ r
⊆ᶜ-∪⁺ʳ l r = ∈ᶜ-∪⁺ʳ l r ∘_

_≢deposit : Cfg → Set
_≢deposit = λ where
  (⟨ _ has _ ⟩at _) → ⊥
  _                 → ⊤

Initial⇒∉ : ⦃ Γ₀ ≢deposit ⦄ → Initial Γ → Γ₀ ∉ᶜ Γ
Initial⇒∉ {Γ = ⟨ _ has _ ⟩at _} ⦃ () ⦄ _ (here refl)
Initial⇒∉ {Γ = l ∣ r} ⦃ ≢dep ⦄ (pˡ , pʳ) =
  ∈ᶜ-∪⁻ l r >≡>
  Sum.[ Initial⇒∉ ⦃ ≢dep ⦄ pˡ
      , Initial⇒∉ ⦃ ≢dep ⦄ pʳ ]

∈ᶜ-resp-≈ : Γ ≈ Γ′ → Γ₀ ∈ᶜ Γ → Γ₀ ∈ᶜ Γ′
∈ᶜ-resp-≈ Γ≈ = ∈-map-resp-↭ to[ Cfg ] Γ≈

∉ᶜ-resp-≈ : Γ ≈ Γ′ → Γ₀ ∉ᶜ Γ → Γ₀ ∉ᶜ Γ′
∉ᶜ-resp-≈ {Γ}{Γ′}{Γ₀} Γ≈ c∉ = c∉ ∘ ∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈)

∉ᶜ-|| : ∀ {A : Set} {f : A → Cfg}
  → (∀ {x} → Γ ∉ᶜ f x)
    --———————————————————————————
  → ∀ xs → Γ ∉ᶜ || map f xs
∉ᶜ-|| Γ∉ (_ ∷ []) Γ∈ = Γ∉ Γ∈
∉ᶜ-|| {f = f} Γ≢ (x ∷ xs@(_ ∷ _)) =
  ∈ᶜ-∪⁻ (f x) (|| map f xs) >≡>
  Sum.[ Γ≢
      , ∉ᶜ-|| Γ≢ xs ]

∈ᶜ-||⇒⊆ᶜ : ∀ {A : Set} {f : A → Cfg} {x} xs
  → x ∈ xs
  → || map f xs ⊆ᶜ Γ
    --———————————————————————————
  → f x ⊆ᶜ Γ
∈ᶜ-||⇒⊆ᶜ                 []               ()          _
∈ᶜ-||⇒⊆ᶜ                 (x ∷ [])         (here refl) Γ⊆ = Γ⊆
∈ᶜ-||⇒⊆ᶜ {Γ = Γ} {f = f} (x ∷ xs@(_ ∷ _)) x∈ Γ⊆ =
  case x∈ of λ where
    (here refl) → Γ⊆ ∘ ∈ᶜ-∪⁺ˡ (f x) (|| map f xs)
    (there x∈)  → ∈ᶜ-||⇒⊆ᶜ {Γ = Γ} xs x∈ (Γ⊆ ∘ ∈ᶜ-∪⁺ʳ (f x) (|| map f xs))

-- ∈ᶜ-||⁺ : ∀ {A : Set} {f : A → Cfg} xs
--   → (∃ λ x → (x ∈ xs) × (Γ ∈ᶜ f x))
--     --———————————————————————————
--   → Γ ∈ᶜ || map f xs
-- ∈ᶜ-||⁺ {f = f} []                (_ , ()        , _)
-- ∈ᶜ-||⁺ {f = f} (.x ∷ [])         (x , here refl , Γ∈) = Γ∈
-- ∈ᶜ-||⁺ {f = f} (.x ∷ xs@(_ ∷ _)) (x , here refl , Γ∈) = ∈ᶜ-∪⁺ˡ (f x) (|| map f xs) Γ∈
-- ∈ᶜ-||⁺ {f = f} (x  ∷ xs@(_ ∷ _)) (y , there y∈  , Γ∈) = ∈ᶜ-∪⁺ʳ (f x) (|| map f xs) (∈ᶜ-||⁺ xs (y , y∈ , Γ∈))

||ˢ_ : Set⟨ Cfg ⟩ → Cfg
||ˢ_ = ||_ ∘ toList

∉ᶜ-||ˢ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {f : A → Cfg}
  → Injective≡ f
  → (∀ {x} → Γ ∉ᶜ f x)
    --———————————————————————————
  → ∀ xs → Γ ∉ᶜ ||ˢ mapˢ f xs
∉ᶜ-||ˢ {Γ = Γ} {f = f} f-inj Γ∉ xs Γ∈
  rewrite nub-from∘to $ L.Uniq.map⁺ f-inj (Set'.uniq xs)
  = ∉ᶜ-|| Γ∉ (toList xs) Γ∈

∈ᶜ-||ˢ⇒⊆ᶜ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {f : A → Cfg} {x} xs
  → Injective≡ f
  → x ∈ˢ xs
  → ||ˢ mapˢ f xs ⊆ᶜ Γ
    --———————————————————————————
  → f x ⊆ᶜ Γ
∈ᶜ-||ˢ⇒⊆ᶜ {Γ = Γ} xs f-inj x∈ ⊆Γ
  rewrite nub-from∘to $ L.Uniq.map⁺ f-inj (Set'.uniq xs)
  = ∈ᶜ-||⇒⊆ᶜ {Γ = Γ} (xs ∙toList) x∈ ⊆Γ

module _ {A : Set} {xs ys : List A} where
  ↭⇒∼set : xs ↭ ys → xs ∼[set] ys
  ↭⇒∼set xs↭ = ⊆⊇⇒∼set (∈-resp-↭ xs↭ , ∈-resp-↭ (↭-sym xs↭))

  module _ ⦃ _ : DecEq A ⦄ where
    ↭⇒≈ˢ : xs ↭ ys → fromList xs ≈ˢ fromList ys
    ↭⇒≈ˢ = from-≈ ∘ ↭⇒∼set

toCfg′-≈ : Γ ≈ Γ′ → to[ Cfg′ ] Γ ∼[set] to[ Cfg′ ] Γ′
toCfg′-≈ = ↭⇒∼set

module _ {X : Set} ⦃ _ : DecEq X ⦄ ⦃ _ : BaseCfg has X ⦄ where
  collectFromBase : Cfg → Set⟨ X ⟩
  collectFromBase = collectFromSet collect ∘ fromList ∘ to[ Cfg′ ]

  collectFromBase⁺ : ∀ {x : X}
    → Any (λ γ → x ∈ˢ collect γ) (to[ Cfg′ ] Γ)
    → x ∈ˢ collectFromBase Γ
  collectFromBase⁺ {Γ} = ∈ˢ-concatMap⁺ collect {fromList $ to[ Cfg′ ] Γ}
                       ∘ Anyˢ-fromList⁺

  collectFromBase≈ : Γ ≈ Γ′ → collectFromBase Γ ≈ collectFromBase Γ′
  collectFromBase≈ {Γ}{Γ′} Γ≈ =
    begin
      collectFromBase Γ
    ≡⟨⟩
      collectFromSet collect (fromList $ to[ Cfg′ ] Γ)
    ≈⟨ collectFromSet≈ collect {fromList $ to[ Cfg′ ] Γ} {fromList $ to[ Cfg′ ] Γ′}
         $ from-≈ $ toCfg′-≈ {Γ}{Γ′} Γ≈ ⟩
      collectFromSet collect (fromList $ to[ Cfg′ ] Γ′)
    ≡⟨⟩
      collectFromBase Γ′
    ∎ where open ≈-Reasoning

  collectFromBase-∪ : ∀ l r →
      collectFromBase (l ∣ r) ≈ collectFromBase l ∪ collectFromBase r
  collectFromBase-∪ l r =
    begin
      collectFromBase (l ∣ r)
    ≡⟨⟩
      collectFromSet collect (fromList $ to[ Cfg′ ] $ l ∣ r)
    ≡⟨⟩
      concatMapˢ collect (fromList $ to[ Cfg′ ] $ l ∣ r)
    ≡⟨⟩
      concatMapˢ collect (fromList $ to[ Cfg′ ] l ++ to[ Cfg′ ] r)
    ≈⟨ ≈ˢ-concatMap⁺ collect
          {fromList $ to[ Cfg′ ] l ++ to[ Cfg′ ] r}
          {fromList (to[ Cfg′ ] l) ∪ fromList (to[ Cfg′ ] r)}
          $ from-++ˢ {xs = to[ Cfg′ ] l}{to[ Cfg′ ] r} ⟩
      concatMapˢ collect (fromList (to[ Cfg′ ] l) ∪ fromList (to[ Cfg′ ] r))
    ≈⟨ concatMapˢ-∪ collect {fromList (to[ Cfg′ ] l)}{fromList (to[ Cfg′ ] r)} ⟩
      concatMapˢ collect (fromList $ to[ Cfg′ ] l) ∪
      concatMapˢ collect (fromList $ to[ Cfg′ ] r)
    ≡⟨⟩
      collectFromSet collect (fromList $ to[ Cfg′ ] l) ∪
      collectFromSet collect (fromList $ to[ Cfg′ ] r)
    ≡⟨⟩
      collectFromBase l ∪ collectFromBase r
    ∎ where open ≈-Reasoning
    -- rewrite
    --   cfgToList-∪ l r
    -- | concatMap-∪ collect (to[ Cfg′ ] l) (to[ Cfg′ ] r)
    -- = refl

  ∈-collect-∪⁻ : ∀ l r {x : X}
    → x ∈ˢ collectFromBase (l ∣ r)
    → x ∈ˢ collectFromBase l ⊎ x ∈ˢ collectFromBase r
  ∈-collect-∪⁻ l r = ∈-∪⁻ _ (collectFromBase l) (collectFromBase r)
                   ∘ collectFromBase-∪ l r .proj₁

  ∈-collect-∪⁺ˡ : ∀ l r {x : X}
    → x ∈ˢ collectFromBase l
    → x ∈ˢ collectFromBase (l ∣ r)
  ∈-collect-∪⁺ˡ l r = collectFromBase-∪ l r .proj₂
                    ∘ ∈-∪⁺ˡ _ (collectFromBase l) (collectFromBase r)

  ∈-collect-∪⁺ʳ : ∀ l r {x : X}
    → x ∈ˢ collectFromBase r
    → x ∈ˢ collectFromBase (l ∣ r)
  ∈-collect-∪⁺ʳ l r = collectFromBase-∪ l r .proj₂
                    ∘ ∈-∪⁺ʳ _ (collectFromBase l) (collectFromBase r)

  module _ {Y : Set} ⦃ _ : DecEq Y ⦄ where
    map∘collectFromBase-∪ : ∀ (f : X → Y) l r
      → mapˢ f (collectFromBase $ l ∣ r)
      ≈ mapˢ f (collectFromBase l) ∪ mapˢ f (collectFromBase r)
    map∘collectFromBase-∪ f l r =
      begin
        mapˢ f (collectFromBase $ l ∣ r)
      ≈⟨ ≈ˢ-map⁺ f {collectFromBase (l ∣ r)} {collectFromBase l ∪ collectFromBase r}
                  $ collectFromBase-∪ l r ⟩
        mapˢ f (collectFromBase l ∪ collectFromBase r)
      ≈⟨ mapˢ-∪ f {collectFromBase l}{collectFromBase r} ⟩
        mapˢ f (collectFromBase l) ∪ mapˢ f (collectFromBase r)
      ∎ where open ≈-Reasoning

    mapMaybe∘collectFromBase-∪ : ∀ (f : X → Maybe Y) l r
      → mapMaybeˢ f (collectFromBase $ l ∣ r)
      ≈ mapMaybeˢ f (collectFromBase l) ∪ mapMaybeˢ f (collectFromBase r)
    mapMaybe∘collectFromBase-∪ f l r =
      begin
        mapMaybeˢ f (collectFromBase $ l ∣ r)
      ≈⟨ ≈ˢ-mapMaybe⁺ f {collectFromBase (l ∣ r)} {collectFromBase l ∪ collectFromBase r}
                    $ collectFromBase-∪ l r ⟩
        mapMaybeˢ f (collectFromBase l ∪ collectFromBase r)
      ≈⟨ mapMaybeˢ-∪ f {collectFromBase l}{collectFromBase r} ⟩
        mapMaybeˢ f (collectFromBase l) ∪ mapMaybeˢ f (collectFromBase r)
      ∎ where open ≈-Reasoning

private variable X Y : Set

module _ ⦃ _ : DecEq X ⦄ where instance
  HBC⇒HC′ : ⦃ BaseCfg has X ⦄ → Cfg′ has X
  HBC⇒HC′ .collect = collectFromSet collect ∘ fromList

  HC′⇒HC : ⦃ Cfg′ has X ⦄ → Cfg has X
  HC′⇒HC ⦃ r ⦄ .collect = collect ⦃ r = r ⦄ ∘ to[ Cfg′ ]

  Hᶜᶠ⇒Hᵗᶜᶠ : ⦃ Cfg has X ⦄ → Cfgᵗ has X
  Hᶜᶠ⇒Hᵗᶜᶠ ⦃ r ⦄ .collect = collect ⦃ r = r ⦄ ∘ cfg

instance
  HNᵃᶜ : Action has Name
  HNᵃᶜ .collect ac with ac
  ... | ♯▷ ad            = names ad
  ... | x ▷ˢ ad          = inj₁ x ∷ˢ names ad
  ... | x ▷ c            = inj₁ x ∷ˢ names c
  ... | x ↔ y ▷⟨ _ , _ ⟩ = fromList $ map inj₁ ⟦ x , y ⟧
  ... | x ▷⟨ _ , _ , _ ⟩ = singleton $ inj₁ x
  ... | x ▷ᵈ _           = singleton $ inj₁ x
  ... | xs , _ ▷ᵈˢ x     = mapˢ inj₁ (x ∷ˢ xs)

  HDᶜᶠ : BaseCfg has DepositRef
  HDᶜᶠ .collect = λ where
    (`⟨ A has v ⟩at x) → singleton (A , v , x)
    _                  → ∅

  HNᶜᶠ : BaseCfg has Name
  HNᶜᶠ .collect = λ where
    -- secrets
    (`⟨ _ ∶ s ♯ _ ⟩)   → singleton (inj₁ s)
    (_ `∶ s ♯ _)       → singleton (inj₁ s)
    -- names
    (`⟨ _ ,   _ ⟩at x) → singleton (inj₂ x)
    (`⟨ _ has _ ⟩at x) → singleton (inj₂ x)
    _                  → ∅

  HAᶜᶠ : BaseCfg has Action
  HAᶜᶠ .collect = λ where
    (_ `auth[ a ]) → singleton a
    _              → ∅

  -- ** See `authorizedHonAds` below
  HAᵇᶜᶠ : BaseCfg has Advertisement
  HAᵇᶜᶠ .collect = λ where
    (A `auth[ ♯▷ ad ]) → if does (A ∈? Hon) then singleton ad else ∅
    _                  → ∅

authorizedActions : ⦃ _ :  X has Action ⦄ → X → Set⟨ Action ⟩
authorizedActions = collect

advertisements : ⦃ _ :  X has Advertisement ⦄ → X → Set⟨ Advertisement ⟩
advertisements = collect
authorizedHonAds = advertisements

authorizedAds : ⦃ _ :  X has Action ⦄ → X → Set⟨ Advertisement ⟩
authorizedAds = mapMaybeˢ (λ where (♯▷ ad) → just ad; _ → nothing)
              ∘ authorizedActions

ids-∪ : ∀ l r → ids (l ∣ r) ≈ ids l ∪ ids r
ids-∪ = mapMaybe∘collectFromBase-∪ isInj₂

∈-ids-∪⁻ : ∀ l r {x : Id} → x ∈ˢ ids (l ∣ r) → (x ∈ˢ ids l) ⊎ (x ∈ˢ ids r)
∈-ids-∪⁻ l r = ∈-∪⁻ _ (ids l) (ids r) ∘ ids-∪ l r .proj₁

∈-ids-∪⁺ˡ : ∀ l r → ids l ⊆ˢ ids (l ∣ r)
∈-ids-∪⁺ˡ l r = ids-∪ l r .proj₂ ∘ ∈-∪⁺ˡ _ (ids l) (ids r)

∈-ids-∪⁺ʳ : ∀ l r → ids r ⊆ˢ ids (l ∣ r)
∈-ids-∪⁺ʳ l r = ids-∪ l r .proj₂ ∘ ∈-∪⁺ʳ _ (ids l) (ids r)

.destruct-∈-ids-∪ : ∀ l r (x∈ : x ∈ˢ ids (l ∣ r)) →
    (∃ λ (x∈ˡ : x ∈ˢ ids l) → x∈ ≡ ∈-ids-∪⁺ˡ l r x∈ˡ)
  ⊎ (∃ λ (x∈ʳ : x ∈ˢ ids r) → x∈ ≡ ∈-ids-∪⁺ʳ l r x∈ʳ)
destruct-∈-ids-∪ {x = x} l r x∈ =
  case destruct-∈ˢ-∪ (ids l) (ids r) $ ids-∪ l r .proj₁ x∈ of λ where
    (inj₁ (x∈ˡ , x∈≡)) → inj₁ (x∈ˡ , ∈ˢ-irr {Xs = ids (l ∣ r)} x∈ (∈-ids-∪⁺ˡ l r x∈ˡ))
    (inj₂ (x∈ʳ , x∈≡)) → inj₂ (x∈ʳ , ∈ˢ-irr {Xs = ids (l ∣ r)} x∈ (∈-ids-∪⁺ʳ l r x∈ʳ))

secrets-∪ : ∀ l r → secrets (l ∣ r) ≈ secrets l ∪ secrets r
secrets-∪ = mapMaybe∘collectFromBase-∪ isInj₁

∈-secrets-∪⁻ : ∀ l r {x : Id} → x ∈ˢ secrets (l ∣ r)
  → (x ∈ˢ secrets l) ⊎ (x ∈ˢ secrets r)
∈-secrets-∪⁻ l r = ∈-∪⁻ _ (secrets l) (secrets r) ∘ secrets-∪ l r .proj₁

∈-secrets-∪⁺ˡ : ∀ l r → secrets l ⊆ˢ secrets (l ∣ r)
∈-secrets-∪⁺ˡ l r = secrets-∪ l r .proj₂ ∘ ∈-∪⁺ˡ _ (secrets l) (secrets r)

∈-secrets-∪⁺ʳ : ∀ l r → secrets r ⊆ˢ secrets (l ∣ r)
∈-secrets-∪⁺ʳ l r = secrets-∪ l r .proj₂ ∘ ∈-∪⁺ʳ _ (secrets l) (secrets r)

deposits-∪ : ∀ l r → deposits (l ∣ r) ≈ deposits l ∪ deposits r
deposits-∪ = collectFromBase-∪

∈-deposits-∪⁻ : ∀ l r {d : DepositRef} → d ∈ˢ deposits (l ∣ r) → (d ∈ˢ deposits l) ⊎ (d ∈ˢ deposits r)
∈-deposits-∪⁻ l r = ∈-∪⁻ _ (deposits l) (deposits r) ∘ deposits-∪ l r .proj₁

∈-deposits-∪⁺ˡ : ∀ l r → deposits l ⊆ˢ deposits (l ∣ r)
∈-deposits-∪⁺ˡ l r = deposits-∪ l r .proj₂ ∘ ∈-∪⁺ˡ _ (deposits l) (deposits r)

∈-deposits-∪⁺ʳ : ∀ l r → deposits r ⊆ˢ deposits (l ∣ r)
∈-deposits-∪⁺ʳ l r = deposits-∪ l r .proj₂ ∘ ∈-∪⁺ʳ _ (deposits l) (deposits r)

secretsOfᶜᶠ : Participant → Cfg → Secrets
secretsOfᶜᶠ A = go
  where
    go : Cfg → Secrets
    go (⟨ B ∶ a ♯ _ ⟩) = if A == B then singleton a else ∅
    go (l ∣ r)         = go l ∪ go r
    go _               = ∅

committedParticipants : Advertisement → Cfg → Set⟨ Participant ⟩
committedParticipants ad = collect
  module ∣committedParticipants∣ where
    instance
      go : BaseCfg has Participant
      go .collect = λ where
        (p `auth[ (♯▷ ad′) ]) → if ad == ad′ then singleton p else ∅
        _                     → ∅

committed⇒authCommit :
   A ∈ˢ committedParticipants ad Γ
   --—————————————————————————————
 → A auth[ ♯▷ ad ] ∈ᶜ Γ
committed⇒authCommit {ad = ad} {Γ = _ auth[ ♯▷ ad′ ]} A∈
  with ad ≟ ad′ | A∈
... | yes refl | here refl = here refl
committed⇒authCommit {A}{ad} {Γ = l ∣ r} A∈
  with ∈-collect-∪⁻ ⦃ it ⦄ ⦃ ∣committedParticipants∣.go ad ⦄ l r A∈
... | inj₁ A∈ˡ = ∈ᶜ-∪⁺ˡ l r (committed⇒authCommit {Γ = l} A∈ˡ)
... | inj₂ A∈ʳ = ∈ᶜ-∪⁺ʳ l r (committed⇒authCommit {Γ = r} A∈ʳ)

module _ (A∈ : A ∈ Hon) where
  committed⇒authAd :
      A ∈ˢ committedParticipants ad Γ
    → ad ∈ˢ authorizedHonAds Γ
  committed⇒authAd {ad} {p auth[ ♯▷ ad′ ]} P
    with ad ≟ ad′ | P
  ... | no _    | ()
  ... | yes ad≡ | here refl
    rewrite dec-true (A ∈? Hon) A∈
    = here ad≡
  committed⇒authAd {ad} {l ∣ r} P
    with ∈-collect-∪⁻ ⦃ it ⦄ ⦃ ∣committedParticipants∣.go ad ⦄ l r P
  ... | inj₁ ∈l = ∈-collect-∪⁺ˡ l r (committed⇒authAd {Γ = l} ∈l)
  ... | inj₂ ∈r = ∈-collect-∪⁺ʳ l r (committed⇒authAd {Γ = r} ∈r)

committedSingle≡ : committedParticipants ad (A auth[ ♯▷ ad ]) ≡ singleton A
committedSingle≡ {ad} rewrite ≟-refl ad = refl

committedPartG≈ : ∀ ps → committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps) ≈ fromList ps
committedPartG≈ [] = ≈-refl {x = ∅}
committedPartG≈ {ad} (p ∷ []) = ≈-reflexive (committedSingle≡ {ad}{p})
committedPartG≈ {ad} (p ∷ ps@(_ ∷ _)) =
  begin
    committedParticipants ad (|| (p auth[ ♯▷ ad ] ∷ map (_auth[ ♯▷ ad ]) ps))
  ≡⟨⟩
    committedParticipants ad (|| (p auth[ ♯▷ ad ] ∷ map (_auth[ ♯▷ ad ]) ps))
  ≈⟨ collectFromBase-∪ ⦃ it ⦄ ⦃ ∣committedParticipants∣.go ad ⦄ (p auth[ ♯▷ ad ]) (|| map (_auth[ ♯▷ ad ]) ps) ⟩
    committedParticipants ad (p auth[ ♯▷ ad ]) ∪ committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)
  ≡⟨ cong (_∪ committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)) (committedSingle≡ {ad}{p}) ⟩
    p ∷ˢ committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)
  ≈⟨ ∪-congˡ {ys = committedParticipants ad (|| map (_auth[ ♯▷ ad ]) ps)}
             {zs = fromList ps}
             {xs = singleton p}
             (committedPartG≈ ps) ⟩
    p ∷ˢ fromList ps
  ≈˘⟨ from-∷ˢ {xs = ps} ⟩
    fromList (p ∷ ps)
  ∎ where open ≈-Reasoning

-- ** Collections of equivalent configurations.

≈⇒names≈ : Γ ≈ Γ′ → Γ ≈⦅ names ⦆ Γ′
≈⇒names≈ {Γ}{Γ′} = collectFromBase≈ {Γ = Γ}{Γ′}

≈⇒ads≈ : Γ ≈ Γ′ → Γ ≈⦅ advertisements ⦆ Γ′
≈⇒ads≈ {Γ}{Γ′} = collectFromBase≈ {Γ = Γ}{Γ′}

≈⇒namesʳ≈ : Γ ≈ Γ′ → Γ ≈⦅ namesʳ ⦆ Γ′
≈⇒namesʳ≈ {Γ}{Γ′} eq = ≈ˢ-mapMaybe⁺ isInj₂ {names Γ}{names Γ′} $ ≈⇒names≈ {Γ}{Γ′} eq

≈⇒namesˡ≈ : Γ ≈ Γ′ → Γ ≈⦅ namesˡ ⦆ Γ′
≈⇒namesˡ≈ {Γ}{Γ′} eq = ≈ˢ-mapMaybe⁺ isInj₁ {names Γ}{names Γ′} $ ≈⇒names≈ {Γ}{Γ′} eq

≈⇒deposits≈ : Γ ≈ Γ′ → Γ ≈⦅ deposits ⦆ Γ′
≈⇒deposits≈ {Γ}{Γ′} = collectFromBase≈ {Γ = Γ}{Γ′}

∈-resp-≈ : ∀ {Z Z′ A : Set} ⦃ _ : DecEq Z ⦄ ⦃ _ : DecEq Z′ ⦄ ⦃ _ : A has Z ⦄ ⦃ _ : ISetoid A ⦄
  → (f : ∀ {X} → ⦃ X has Z ⦄ → X → Set⟨ Z′ ⟩)
  → (∀ {a a′ : A} → a ≈ a′ → a ≈⦅ f ⦆ a′)
  → ∀ (z : Z′) → (λ ◆ → z ∈ˢ f ◆) Respects (Rel A _ ∋ _≈_)
∈-resp-≈ _ ≈⇒≈ _ eq = ≈⇒≈ eq .proj₁

∈ads-resp-≈      = ∈-resp-≈ advertisements (λ {Γ}{Γ′} → ≈⇒ads≈      {Γ}{Γ′})
∈names-resp-≈    = ∈-resp-≈ names          (λ {Γ}{Γ′} → ≈⇒names≈    {Γ}{Γ′})
∈namesˡ-resp-≈   = ∈-resp-≈ namesˡ         (λ {Γ}{Γ′} → ≈⇒namesˡ≈   {Γ}{Γ′})
∈namesʳ-resp-≈   = ∈-resp-≈ namesʳ         (λ {Γ}{Γ′} → ≈⇒namesʳ≈   {Γ}{Γ′})
∈deposits-resp-≈ = ∈-resp-≈ deposits       (λ {Γ}{Γ′} → ≈⇒deposits≈ {Γ}{Γ′})

-- ** name helpers

-- ≈-sym∘≈⇒names≈ :
--     (Γ≈ : Γ ≈ Γ′)
--     --——————————————————————————
--   → ≈-sym (≈⇒names≈ {Γ}{Γ′} Γ≈)
--   ≡ ≈⇒names≈ {Γ′}{Γ} (≈-sym Γ≈)
-- ≈-sym∘≈⇒names≈ = {!!} -- ↭-sym∘concatMap⁺ names

-- ≈-sym∘≈⇒namesʳ≈ :
--     (Γ≈ : Γ ≈ Γ′)
--     --——————————————————————————
--   → ≈-sym (≈⇒namesʳ≈ {Γ}{Γ′} Γ≈)
--   ≡ ≈⇒namesʳ≈ {Γ′}{Γ} (≈-sym Γ≈)
-- ≈-sym∘≈⇒namesʳ≈ {Γ}{Γ′} Γ≈ =
--   begin
--     ≈-sym (≈⇒namesʳ≈ {Γ}{Γ′} Γ≈)
--   ≡⟨ ↭-sym∘mapMaybe⁺ isInj₂ $ ≈⇒names≈ {Γ}{Γ′} Γ≈ ⟩
--     ≈ˢ-mapMaybe⁺ isInj₂ (≈-sym $ ≈⇒names≈ {Γ}{Γ′} Γ≈)
--   ≡⟨ cong (≈ˢ-mapMaybe⁺ isInj₂) $ ≈-sym∘≈⇒names≈ {Γ}{Γ′} Γ≈ ⟩
--     ≈⇒namesʳ≈ {Γ′}{Γ} (≈-sym Γ≈)
--   ∎ where open ≡-Reasoning

deposit∈Γ⇒namesʳ : ∀ {Γ}
  → ⟨ A has v ⟩at x ∈ᶜ Γ
  → x ∈ˢ namesʳ Γ
deposit∈Γ⇒namesʳ {A} {v} {x} {` _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ , _ ⟩at _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ has _ ⟩at .x} (here refl) = here refl
deposit∈Γ⇒namesʳ {A} {v} {x} {_ auth[ _ ]} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ ∶ _ ♯ _ ⟩} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {_ ∶ _ ♯ _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {l ∣ r} d∈
  with ∈ᶜ-∪⁻ l r d∈
... | inj₁ d∈ˡ = let _ , x∈ , d≡ = ∈ˢ-mapMaybe⁻ isInj₂ {xs = names l} (deposit∈Γ⇒namesʳ {Γ = l} d∈ˡ)
                 in ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣ r)} (∈-collect-∪⁺ˡ l r x∈) d≡
... | inj₂ d∈ʳ = let _ , x∈ , d≡ = ∈ˢ-mapMaybe⁻ isInj₂ {xs = names r} (deposit∈Γ⇒namesʳ {Γ = r} d∈ʳ)
                 in ∈ˢ-mapMaybe⁺ isInj₂ {xs = names (l ∣ r)} (∈-collect-∪⁺ʳ l r x∈) d≡

-- namesʳ-∥map-authDestroy : ∀ (ds : Set⟨ Participant × Value × Id ⟩)
--   → mapˢ (proj₂ ∘ proj₂) ds ⊆ˢ namesʳ (|| map (uncurry₃ ⟨_has_⟩at_) (toList ds))
-- namesʳ-∥map-authDestroy (_ ∷ []) (here refl) = here refl
-- namesʳ-∥map-authDestroy (_ ∷ _ ∷ _) (here refl) = here refl
-- namesʳ-∥map-authDestroy ((Bᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) (there d∈) = there $ (namesʳ-∥map-authDestroy ds) d∈

-- private
--   n≡ : ∀ {A : Set} {P Q : A → Cfg}
--     → (∀ x → Null $ namesʳ (Q x) )
--     → (xs : List A)
--     → namesʳ (|| map (λ x → P x ∣ Q x) xs)
--     ≡ namesʳ (|| map P xs)
--   n≡ ∀x [] = refl
--   n≡ {P = P}{Q} ∀x (x₁ ∷ []) = P∣Q≡
--     where
--       P∣Q≡ : namesʳ (P x₁ ∣ Q x₁) ≡ namesʳ (P x₁)
--       P∣Q≡ rewrite mapMaybe∘collectFromBase-∪ isInj₂ (P x₁) (Q x₁)
--                 | ∀x x₁
--                 | L.∪-identityʳ (namesʳ $ P x₁)
--                 = refl
--   n≡ {P = P}{Q} ∀x (x₁ ∷ xs@(_ ∷ _)) =
--     begin
--       namesʳ (|| (P x₁ ∣ Q x₁ ∷ map (λ x → P x ∣ Q x) xs))
--     ≡⟨⟩
--       namesʳ (P x₁ ∣ Q x₁ ∣ || map (λ x → P x ∣ Q x) xs)
--     ≡⟨ mapMaybe∘collectFromBase-∪ isInj₂ (P x₁ ∣ Q x₁) (|| map (λ x → P x ∣ Q x) xs) ⟩
--       namesʳ (P x₁ ∣ Q x₁) ∪ namesʳ (|| map (λ x → P x ∣ Q x) xs)
--     ≡⟨ cong (_∪ namesʳ (|| map (λ x → P x ∣ Q x) xs)) P∣Q≡ ⟩
--       namesʳ (P x₁) ∪ namesʳ (|| map (λ x → P x ∣ Q x) xs)
--     ≡⟨ cong (namesʳ (P x₁) ∪_) $ n≡ {P = P}{Q} ∀x xs ⟩
--       namesʳ (P x₁) ∪ namesʳ (|| map P xs)
--     ≡⟨ sym $ mapMaybe∘collectFromBase-∪ isInj₂ (P x₁) (|| map P xs) ⟩
--       namesʳ (|| (P x₁ ∷ map P xs))
--     ∎
--     where
--       open ≡-Reasoning

--       P∣Q≡ : namesʳ (P x₁ ∣ Q x₁) ≡ namesʳ (P x₁)
--       P∣Q≡ rewrite collectFromBase-∪ {X = Name} (P x₁) (Q x₁)
--                 | mapMaybe-∪ isInj₂ (names $ P x₁) (names $ Q x₁)
--                 | ∀x x₁
--                 | L.∪-identityʳ (namesʳ $ P x₁)
--                 = refl

-- namesʳ-∥map-destroy : ∀ (ds : List (Participant × Value × Id)) → let xs = map (proj₂ ∘ proj₂) ds in
--   xs ⊆ namesʳ (|| map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds))
-- namesʳ-∥map-destroy {y = y} ds {x} x∈ = qed
--   where
--     PVI = Participant × Value × Id
--     x̂ = map (proj₂ ∘ proj₂) ds
--     eds = enumerate ds

--     P : PVI → Cfg
--     P (Aᵢ , vᵢ , xᵢ) = ⟨ Aᵢ has vᵢ ⟩at xᵢ

--     P′ : ∀ {A : Set} → A × PVI → Cfg
--     P′ = P ∘ proj₂

--     Q P∣Q : Index ds × PVI → Cfg
--     Q (i , Aᵢ , vᵢ , xᵢ) = Aᵢ auth[ x̂ , ‼-map {xs = ds} i ▷ᵈˢ y ]
--     P∣Q x = P′ x ∣ Q x

--     h : namesʳ (|| map P∣Q eds)
--       ≡ namesʳ (|| map P′ eds)
--     h = n≡ {A = Index ds × PVI} {P = P′} {Q = Q} (λ _ → refl) eds

--     -- [BUG] if I replace `enumerate ds` with `eds` I get an error!?
--     h′ : ∀ (ds : List PVI) → map P′ (enumerate ds) ≡ map P ds
--     h′ [] = refl
--     h′ (pvi ∷ ds) = cong (_ ∷_) qed
--       where
--         rec : map P′ (zip (L.tabulate {n = length ds} (fsuc ∘ id)) ds)
--             ≡ map (P′ ∘ map₁ fsuc) (zip (L.tabulate {n = length ds} id) ds)
--         rec = map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate {m = length ds} ds {P = P′} {f = id}

--         qed : map P′ (zip (L.tabulate {n = length ds} fsuc) ds)
--             ≡ map P ds
--         qed = trans rec (h′ ds)

--     qed : x ∈ namesʳ (|| map P∣Q eds)
--     qed rewrite h | h′ ds = namesʳ-∥map-authDestroy ds x∈

-- namesʳ-∥map-authCommit : ∀ {secrets : List (Secret × Maybe ℕ)} → let (as , ms) = unzip secrets in
--     as ⊆ namesˡ (|| map (uncurry ⟨ A ∶_♯_⟩) secrets)
-- namesʳ-∥map-authCommit {secrets = `∅ᶜ} ()
-- namesʳ-∥map-authCommit {secrets = (_ , _) ∷ []} (here refl) = here refl
-- namesʳ-∥map-authCommit {secrets = (_ , _) ∷ ss@(_ ∷ _)} (here refl) = here refl
-- namesʳ-∥map-authCommit {secrets = _ ∷ ss@(_ ∷ _)} (there a∈) = there (namesʳ-∥map-authCommit {secrets = ss} a∈)

x∈vcis⇒¬fresh : ∀ {vcis : List (Value × Contracts × Id)}
  → ⟨ c , v ⟩at x ∈ᶜ || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis
    --—————————————————————————————————————————————————
  → x ∈ select₃ (unzip₃ vcis)
x∈vcis⇒¬fresh {vcis = _ ∷ []}         = λ where
  (here refl) → here refl
x∈vcis⇒¬fresh {vcis = _ ∷ vs@(_ ∷ _)} = λ where
  (here refl) → here refl
  (there c∈)  → there $ x∈vcis⇒¬fresh {vcis = vs} c∈

c∈vcis⇒ : ∀ {vcis : List (Value × Contracts × Id)}
  → ⟨ c , v ⟩at x ∈ᶜ || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis
    --———————————————————————————————————————————————————————
  → c ∈ proj₁ (proj₂ $ unzip₃ vcis)
c∈vcis⇒ {vcis = _ ∷ []}         = λ where
  (here refl) → here refl
c∈vcis⇒ {vcis = _ ∷ vs@(_ ∷ _)} = λ where
  (here refl) → here refl
  (there c∈)  → there $ c∈vcis⇒ {vcis = vs} c∈

c∈vcis⇒′ : ∀ {vcis : List (Value × Contracts × Id)} →
  let
    (vs , cs , _) = unzip₃ vcis
    vcs = zip vs cs
  in
    ⟨ c , v ⟩at x ∈ᶜ || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis
    --————————————————————————————————————————————————————————
  → c ∈ map proj₂ vcs
c∈vcis⇒′ {vcis = _ ∷ []}         = λ where
  (here refl) → here refl
c∈vcis⇒′ {vcis = _ ∷ vs@(_ ∷ _)} = λ where
  (here refl) → here refl
  (there c∈)  → there $ c∈vcis⇒′ {vcis = vs} c∈

-- x∈vcis⇒ : ∀ {vcis : List (Value × Contracts × Id)}
--   → x ∈ ids (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis)
--   → x ∈ select₃ (unzip₃ vcis)
-- x∈vcis⇒ {vcis = _ ∷ []}         = λ where
--   (here refl) → here refl
-- x∈vcis⇒ {vcis = _ ∷ vs@(_ ∷ _)} = λ where
--   (here refl) → here refl
--   (there c∈)  → there $ x∈vcis⇒ {vcis = vs} c∈

-- Base/Composite configurations.

IsComposite IsBase : Pred₀ Cfg
IsComposite = λ where
  (_ ∣ _) → ⊤
  _       → ⊥
IsBase = λ where
  ∅ᶜ      → ⊥
  (_ ∣ _) → ⊥
  _       → ⊤

¬base×composite : ∀ Γ → ¬ (IsBase Γ × IsComposite Γ)
¬base×composite = λ where
  ∅ᶜ      (() , _)
  (_ ∣ _) (() , _)
  (` _)             (_ , ())
  (⟨ _ has _ ⟩at _) (_ , ())
  (⟨ _ , _ ⟩at _)   (_ , ())
  (_ auth[ _ ])     (_ , ())
  (⟨ _ ∶ _ ♯ _ ⟩)   (_ , ())
  (_ ∶ _ ♯ _)       (_ , ())

instance
  Split-∣ : (∃ IsComposite) -splitsInto- Cfg
  Split-∣ .mkSplit ((l ∣ r) , tt) = l , r

IsBase-BaseCfg  : ∀ (`γ : BaseCfg)
  → IsBase (to[ Cfg ] `γ)
IsBase-BaseCfg = λ where
  (`` _)             → tt
  (`⟨ _ , _ ⟩at _)   → tt
  (`⟨ _ has _ ⟩at _) → tt
  (_ `auth[ _ ])     → tt
  `⟨ _ ∶ _ ♯ _ ⟩     → tt
  (_ `∶ _ ♯ _)       → tt

∈ᶜ⇒IsBase : ∀ {γ Γ}
  → γ ∈ᶜ Γ
  → IsBase γ
∈ᶜ⇒IsBase {γ = γ} γ∈
  with `γ , `γ∈ , eq ← ∈-map⁻ to[ Cfg ] γ∈
  = subst IsBase (sym eq) $ IsBase-BaseCfg `γ

instance
  Squashed-IsBase : ∀ {Γ} → · (IsBase Γ)
  Squashed-IsBase {Γ} .∀≡ with Γ
  ... | ∅ᶜ              = λ ()
  ... | _ ∣ _           = λ ()
  ... | ` _             = λ tt tt → refl
  ... | ⟨ _ has _ ⟩at _ = λ tt tt → refl
  ... | ⟨ _ , _ ⟩at _   = λ tt tt → refl
  ... | _ auth[ _ ]     = λ tt tt → refl
  ... | ⟨ _ ∶ _ ♯ _ ⟩   = λ tt tt → refl
  ... | _ ∶ _ ♯ _       = λ tt tt → refl

instance
  Cfg↝BaseCfg : Cfg ⁇ IsBase ↝ BaseCfg
  Cfg↝BaseCfg .toBecause (` ad)            = `` ad
  Cfg↝BaseCfg .toBecause (⟨ c , v ⟩at x)   = `⟨ c , v ⟩at x
  Cfg↝BaseCfg .toBecause (⟨ A has v ⟩at x) = `⟨ A has v ⟩at x
  Cfg↝BaseCfg .toBecause (A auth[ a ])     = A `auth[ a ]
  Cfg↝BaseCfg .toBecause (⟨ A ∶ s ♯ mn ⟩)  = `⟨ A ∶ s ♯ mn ⟩
  Cfg↝BaseCfg .toBecause (A ∶ s ♯ n)       = A `∶ s ♯ n

private
  _ : ⌞ ⟨ c , v ⟩at x ⌟ ≡ `⟨ c , v ⟩at x
  _ = refl

IsBase-to[Cfg] : ∀ (β : BaseCfg) → IsBase (to[ Cfg ] β)
IsBase-to[Cfg] = λ where
  (`` _) → tt
  (`⟨ _ , _ ⟩at _) → tt
  (`⟨ _ has _ ⟩at _) → tt
  (_ `auth[ _ ]) → tt
  `⟨ _ ∶ _ ♯ _ ⟩ → tt
  (_ `∶ _ ♯ _) → tt

to[Cfg]-inverseˡ : ∀ (β : BaseCfg) →
  ((λ _ → ⌞ _ ⊣ IsBase-to[Cfg] β ⌟) ∘ to[ Cfg ]) β ≡ β
to[Cfg]-inverseˡ = λ where
  (`` _)             → refl
  (`⟨ _ , _ ⟩at _)   → refl
  (`⟨ _ has _ ⟩at _) → refl
  (_ `auth[ _ ])     → refl
  `⟨ _ ∶ _ ♯ _ ⟩     → refl
  (_ `∶ _ ♯ _)       → refl

to[Cfg]-inverseʳ : ∀ (γ : Cfg) (base-γ : IsBase γ) →
  (to[ Cfg ] ∘ (λ _ → ⌞ _ ⊣ base-γ ⌟)) γ ≡ γ
to[Cfg]-inverseʳ = λ where
  (` _)             _ → refl
  (⟨ _ , _ ⟩at _)   _ → refl
  (⟨ _ has _ ⟩at _) _ → refl
  (_ auth[ _ ])     _ → refl
  ⟨ _ ∶ _ ♯ _ ⟩     _ → refl
  (_ ∶ _ ♯ _)       _ → refl

open import Prelude.InferenceRules
open import Prelude.Tactics.Rewrite

toCfg≡ : ∀ γ (β : BaseCfg) →
 (γ≡ : γ ≡ to[ Cfg ] β) →
 ──────────────────────────────────────────────
 let base-γ = ⟪ IsBase ⟫ γ≡ ~: IsBase-to[Cfg] β
 in ⌞ γ ⊣  base-γ ⌟ ≡ β
toCfg≡ (` )              (`` _)             refl = refl
toCfg≡ (⟨ _ , _ ⟩at _)   (`⟨ _ , _ ⟩at _)   refl = refl
toCfg≡ (⟨ _ has _ ⟩at _) (`⟨ _ has _ ⟩at _) refl = refl
toCfg≡ (_ auth[ _ ])     (_ `auth[ _ ])     refl = refl
toCfg≡ ⟨ _ ∶ _ ♯ _ ⟩     `⟨ _ ∶ _ ♯ _ ⟩     refl = refl
toCfg≡ (_ ∶ _ ♯ _)       (_ `∶ _ ♯ _)       refl = refl

∈-Cfg′ : ∀ γ Γ
  → (γ∈ : γ ∈ᶜ Γ)
  → ⌞ γ ⊣ ∈ᶜ⇒IsBase {Γ = Γ} γ∈ ⌟ ∈ to[ Cfg′ ] Γ
∈-Cfg′ γ Γ γ∈ =
  let β , β∈ , eq = L.Mem.∈-map⁻ to[ Cfg ] γ∈
  in L.Any.map (trans $ toCfg≡ _ _ eq) β∈

∈-resp-≈∘∈-Cfg′ : ∀ γ Γ Γ′
  → (Γ≈ : Γ ≈ Γ′)
  → (γ∈ : γ ∈ᶜ Γ)
  --————————————————————————————————————
  → ( ∈-Cfg′ _ Γ′          -- ⌞ γ ⌟ ∈ to[ Cfg′ ] Γ′
    ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈ -- γ ∈ᶜ Γ′
    ) γ∈                   -- γ ∈ᶜ Γ
  ≡ ( ∈-resp-↭ Γ≈ -- ⌞ γ ⌟ ∈ to[ Cfg′ ] Γ′
    ∘ ∈-Cfg′ _ Γ  -- ⌞ γ ⌟ ∈ to[ Cfg′]  Γ
    ) γ∈          -- γ ∈ᶜ Γ
∈-resp-≈∘∈-Cfg′ γ Γ Γ′ Γ≈ γ∈
  = begin
    ( ∈-Cfg′ _ Γ′                  -- β ∈ to[ Cfg′ ] Γ′
    ∘ ∈-resp-↭ (map⁺ to[ Cfg ] Γ≈) -- γ ∈ᶜ Γ′
    ) γ∈                           -- γ ∈ᶜ Γ
  ≡⟨⟩
    ( (λ{ (β , β∈ , eq) → L.Any.map (trans $ toCfg≡ _ _ eq) β∈})
    ∘ ∈-map⁻ to[ Cfg ]
    ∘ ∈-resp-↭ (map⁺ to[ Cfg ] Γ≈)
    ) γ∈
  ≡⟨ cong (λ{ (β , β∈ , eq) → L.Any.map (trans $ toCfg≡ _ _ eq) β∈})
        $ ∈-map⁻∘∈-resp-↭∘map⁺ to[ Cfg ] Γ≈ γ∈ ⟩
    ( (λ{ (β , β∈ , eq) → L.Any.map (trans $ toCfg≡ _ _ eq) β∈})
    ∘ map₂′ (map₁ $ ∈-resp-↭ Γ≈)
    ∘ ∈-map⁻ to[ Cfg ]
    ) γ∈
  ≡⟨⟩
    ( (λ{ (β , β∈ , eq) → L.Any.map (trans $ toCfg≡ _ _ eq) (∈-resp-↭ Γ≈ β∈)})
    ∘ ∈-map⁻ to[ Cfg ]
    ) γ∈
  ≡⟨ (let β , β∈ , eq = ∈-map⁻ to[ Cfg ] γ∈
      in Any-map∘∈-resp-↭ (trans $ toCfg≡ γ β eq) Γ≈ β∈) ⟩
    ( (λ{ (β , β∈ , eq) → ∈-resp-↭ Γ≈ $ L.Any.map (trans $ toCfg≡ _ _ eq) β∈})
    ∘ ∈-map⁻ to[ Cfg ]
    ) γ∈
  ≡⟨⟩
    ( ∈-resp-↭ Γ≈ -- β ∈ to[Cfg′] Γ′
    ∘ ∈-Cfg′ _ Γ  -- β ∈ to[Cfg′] Γ
    ) γ∈          -- γ ∈ᶜ Γ
  ∎ where open ≡-Reasoning
