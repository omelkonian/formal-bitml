open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.ToList
open import Prelude.Lists
open import Prelude.General hiding (_⊢_)
open import Prelude.Nary
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Measurable
open import Prelude.ToN

module BitML.Properties.Helpers
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest

_∙head : (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ′) → Cfgᵗ
_∙head = λ where
  (Γₜ ∎)             → Γₜ
  (Γₜ —→⟨ _ ⟩ _ ⊢ _) → Γₜ

mutual
  allStatesᵗ⁺ : (Γₜ —[ αs ]↠ₜ Γₜ′) → List⁺ Cfgᵗ
  allStatesᵗ⁺ {Γₜ} Γ↠ = Γₜ ∷ (case Γ↠ of λ where
    (.Γₜ ∎)              → []
    (.Γₜ —→⟨ _ ⟩ _ ⊢ tr) → allStatesᵗ tr)

  allStatesᵗ : (Γₜ —[ αs ]↠ₜ Γₜ′) → List Cfgᵗ
  allStatesᵗ = toList ∘ allStatesᵗ⁺

module _ (Γ↠ : Γₜ —[ αs ]↠ₜ Γₜ′) where
  allStates⁺ : List⁺ Cfg
  allStates⁺ = L.NE.map cfg $ allStatesᵗ⁺ Γ↠

  allStates : List Cfg
  allStates = toList allStates⁺

  allTransitionsᵗ : List (Cfgᵗ × Cfgᵗ)
  allTransitionsᵗ = pairs $ allStatesᵗ Γ↠

  allTransitions : List (Cfg × Cfg)
  allTransitions = map (map₁₂ cfg) allTransitionsᵗ

∈⇒∈ᵗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  →         Γ      ∈ allStates  tr
  → ∃ λ t → Γ at t ∈ allStatesᵗ tr
∈⇒∈ᵗ tr Γ∈ with _ , Γₜ∈ , refl ← ∈⁺-map⁻ cfg {xs = allStatesᵗ⁺ tr} Γ∈ = -, Γₜ∈

∈ᵗ⇒∈ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → Γ at t ∈ allStatesᵗ tr
  → Γ      ∈ allStates  tr
∈ᵗ⇒∈ tr = ∈⁺-map⁺ cfg {xs = allStatesᵗ⁺ tr}

×∈⇒×∈ᵗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  →                  (Γ ,      Γ′)       ∈ allTransitions  tr
  → ∃ λ t → ∃ λ t′ → (Γ at t , Γ′ at t′) ∈ allTransitionsᵗ tr
×∈⇒×∈ᵗ tr ×∈
  with _ , xy∈ᵗ , refl ← L.Mem.∈-map⁻ (map₁₂ cfg) {xs = allTransitionsᵗ tr} ×∈
  = -, -, xy∈ᵗ

×∈ᵗ⇒×∈ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → (Γ at t , Γ′ at t′) ∈ allTransitionsᵗ tr
  → (Γ ,      Γ′)       ∈ allTransitions  tr
×∈ᵗ⇒×∈ tr = L.Mem.∈-map⁺ (map₁₂ cfg) {xs = allTransitionsᵗ tr}

-- ∈-allTransitionsᵗ⁺ :
--     (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″)
--   → (Γₜ ∈ allStatesᵗ tr)
--     --—————————————————————————————————————————
--   → Σ Cfgᵗ λ Γₜ′ → (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr
-- ∈-allTransitionsᵗ⁺ (_ ∎) = λ where
--   (here refl) → -, here refl
-- ∈-allTransitionsᵗ⁺ (_ —→⟨ _ ⟩ _ ⊢ tr) = λ where
--   (here refl) → -, here refl
--   (there x∈)  → let Γₜ′ , y∈ = ∈-allTransitionsᵗ⁺ tr x∈ in Γₜ′ , there y∈

∈-allTransitionsᵗ⁻ :
    (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″)
  → (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr
    --————————————————————————
  → (Γₜ ∈ allStatesᵗ tr)
  × (Γₜ′ ∈ allStatesᵗ tr)
∈-allTransitionsᵗ⁻ (_ —→⟨ _ ⟩ _ ⊢ tr) = λ where
  (here refl) → here refl , there (here refl)
  (there xy∈) → let x∈ , y∈ = ∈-allTransitionsᵗ⁻ tr xy∈ in there x∈ , there y∈

∈-allTransitions⁻ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → (Γ , Γ′) ∈ allTransitions tr
    --————————————————————————
  → (Γ ∈ allStates tr)
  × (Γ′ ∈ allStates tr)
∈-allTransitions⁻ tr xy∈ =
  let
    _ , _ , xy∈ᵗ = ×∈⇒×∈ᵗ tr xy∈
    x∈ᵗ , y∈ᵗ = ∈-allTransitionsᵗ⁻ tr xy∈ᵗ
  in
    ∈ᵗ⇒∈ tr x∈ᵗ , ∈ᵗ⇒∈ tr y∈ᵗ

allStatesᵗ⁺-∷ : ∀ {x′ y y′ z}
  → (Γ→ : x′ —[ α ]→ₜ y′)
  → (eq : Γₜ ≈ x′ × y ≈ y′)
  → (Γ↠ : y —[ αs ]↠ₜ z)
  → allStatesᵗ⁺ (Γₜ —→ₜ⟨ Γ→ ⟩ eq ⊢ Γ↠) ≡ (Γₜ ∷⁺ allStatesᵗ⁺ Γ↠)
allStatesᵗ⁺-∷ Γ→ eq Γ↠ = refl

allStatesᵗ⁺-∷ʳ : ∀ {x y y′}
  → (Γ↞ : x —[ αs ]↠ₜ y)
  → (Γ← : y′ —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × y ≈ y′)
  → allStatesᵗ⁺ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞) ≡ (allStatesᵗ⁺ Γ↞ ⁺∷ʳ Γₜ)
allStatesᵗ⁺-∷ʳ (_ ∎) _ _ = refl
allStatesᵗ⁺-∷ʳ {Γₜ = Γₜ} (x —→⟨ Γ←′ ⟩ eq′ ⊢ Γ↞) Γ← eq =
  begin≡
    allStatesᵗ⁺ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ x —→ₜ⟨ Γ←′ ⟩ eq′ ⊢ Γ↞)
  ≡⟨⟩
    allStatesᵗ⁺ (x —→ₜ⟨ Γ←′ ⟩ eq′ ⊢ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞))
  ≡⟨⟩
    x ∷⁺ allStatesᵗ⁺ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞)
  ≡⟨ cong (x ∷⁺_) (allStatesᵗ⁺-∷ʳ Γ↞ Γ← eq) ⟩
    (x ∷⁺ allStatesᵗ⁺ Γ↞) ⁺∷ʳ Γₜ
  ≡⟨⟩
    allStatesᵗ⁺ (x —→ₜ⟨ Γ←′ ⟩ eq′ ⊢ Γ↞) ⁺∷ʳ Γₜ
  ∎≡
  where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

_~[_]→ₜ_ : Cfgᵗ → Label → Cfgᵗ → Set
x ~[ α ]→ₜ y =
  ∃ λ x′ → ∃ λ y′ →
      (x ≈ x′ × y ≈ y′)
    × (x′ —[ α ]→ₜ y′)

∃[_∋_]′ : Γₜ —[ αs ]↠ₜ Γₜ′ → (Γₜ —[ αs ]↠ₜ Γₜ′ → Rel₀ Cfg) → Set
∃[ Γ↠ ∋ P ]′
  = ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′
  → ((x , y) ∈ allTransitions Γ↠)
  × (x ≈ x′ × y ≈ y′)
  × P Γ↠ x′ y′

∃[_∋_] : Γₜ —[ αs ]↠ₜ Γₜ′ → Rel₀ Cfg → Set
∃[ Γ↠ ∋ P ] = ∃[ Γ↠ ∋ const P ]′

∃[_∋ᵗ_]′ : Γₜ —[ αs ]↠ₜ Γₜ′ → (Γₜ —[ αs ]↠ₜ Γₜ′ → Rel₀ Cfgᵗ) → Set
∃[ Γ↠ ∋ᵗ P ]′
  = ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′
  → ((x , y) ∈ allTransitionsᵗ Γ↠)
  × (x ≈ x′ × y ≈ y′)
  × P Γ↠ x′ y′

∃[_∋ᵗ_] : Γₜ —[ αs ]↠ₜ Γₜ′ → Rel₀ Cfgᵗ → Set
∃[ Γ↠ ∋ᵗ P ] = ∃[ Γ↠ ∋ᵗ const P ]′

zoomP : ∀ {P : Pred₀ Label}
  → (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → Any P αs
    --———————————————————————————————————
  → ∃[ tr ∋ᵗ (λ Γₜ Γₜ′ → ∃ λ α → P α × (Γₜ —[ α ]→ₜ Γₜ′)) ]
zoomP (_—→⟨_⟩_⊢_ x {x′}{y}{y′} Γ→ eq Γ↠) (here Pα)
  rewrite allStatesᵗ⁺-∷ {Γₜ = x} Γ→ eq Γ↠
  = -, -, -, -, here refl , eq , (-, Pα , Γ→)
zoomP (_ —→⟨ _ ⟩ _ ⊢ Γ↠) (there α∈)
  with _ , _ , _ , _ , xy∈ , ≈Γ→ ← zoomP Γ↠ α∈
    = -, -, -, -, there xy∈ , ≈Γ→

zoom :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → α ∈ αs
    --———————————————————————————————————
  → ∃[ tr ∋ᵗ _—[ α ]→ₜ_ ]
zoom {α = α} Γ↠ α∈
  with _ , _ , _ , _ , xy∈ , x≈ , .α , refl , Γ→ ← zoomP Γ↠ α∈
     = -, -, -, -, xy∈ , x≈ , Γ→

namesʳ⊆deposits :
    x ∈ namesʳ g
  → Σ Participant λ A → Σ Value λ v →
      (A , v , x) ∈ deposits g
namesʳ⊆deposits {x} {A :? v at x} (here refl) = A , v , here refl
namesʳ⊆deposits {x} {A :! v at x} (here refl) = A , v , here refl
namesʳ⊆deposits {x} {l ∣∣ r} x∈
  rewrite mapMaybe-++ isInj₂ (names l) (names r)
  with L.Mem.∈-++⁻ (namesʳ l) x∈
namesʳ⊆deposits {x} {l ∣∣ r} x∈ | inj₁ x∈ˡ
  with A , v , d∈ ← namesʳ⊆deposits {g = l} x∈ˡ
  with _ , td∈ , refl ← L.Mem.∈-map⁻ proj₂ d∈
     = A , v , L.Mem.∈-map⁺ proj₂ (L.Mem.∈-++⁺ˡ td∈)
namesʳ⊆deposits {x} {l ∣∣ r} x∈ | inj₂ x∈ʳ
  with A , v , d∈ ← namesʳ⊆deposits {g = r} x∈ʳ
  with _ , td∈ , refl ← L.Mem.∈-map⁻ proj₂ d∈
     = A , v , L.Mem.∈-map⁺ proj₂ (L.Mem.∈-++⁺ʳ _ td∈)

deposits⊆namesʳ :
    (A , v , x) ∈ deposits Γ
  → x ∈ namesʳ Γ
deposits⊆namesʳ {A} {v} {x} {⟨ A has v ⟩at x} (here refl) = here refl
deposits⊆namesʳ {A} {v} {x} {l ∣ r} d∈
  rewrite mapMaybe∘collectFromBase-++ {X = Name} isInj₂ l r
  rewrite collectFromBase-++ {X = DepositRef} l r
  with L.Mem.∈-++⁻ (deposits l) d∈
... | inj₁ x∈ˡ = L.Mem.∈-++⁺ˡ $ deposits⊆namesʳ {Γ = l} x∈ˡ
... | inj₂ x∈ʳ = L.Mem.∈-++⁺ʳ _ $ deposits⊆namesʳ {Γ = r} x∈ʳ

deposits⊆⇒namesʳ⊆ :
    deposits ad ⊆ deposits Γ
  → namesʳ ad ⊆ namesʳ Γ
deposits⊆⇒namesʳ⊆ {ad}{Γ} d⊆
  = deposits⊆namesʳ {Γ = Γ}
  ∘ d⊆
  ∘ (proj₂ ∘ proj₂)
  ∘ namesʳ⊆deposits {g = ad .G}

¬Delay : Γ —[ delay⦅ δ ⦆ ]↛ Γ′
¬Delay ([C-Control] _ _ _ ())

-- NB: typechecking pattern-match coverage for this is slooooow
postulate
  cvDestroys :
      x ∉ ids Γ
    → ⟨ [ d ] , v ⟩at x ∣ Γ —[ α ]→ Γ′
    → cv α ≡ just x
      --—————————————————————————————————
    → x ∉ ids Γ′
{-
cvDestroys y∉ step cv≡ y∈
  with step | cv≡
... | [C-Withdraw] fresh-y | refl =
  case y∈ of λ where
    (here refl) → fresh-y $ here refl
    (there y∈Γ) → y∉ y∈Γ
... | [C-PutRev] {Γ′}{z}{y}{p}{c}{v} {ds = ds}{ss} fresh-z _ | refl =
  let
    (_ , vs , xs) = unzip₃ ds
    (_ , as , _)  = unzip₃ ss
    Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
    Δ = || map (uncurry₃ _∶_♯_) ss
    ΔΓ′ = Δ ∣ Γ′
  in case y∈ of λ where
       (here refl)  → fresh-z $ here refl
       (there y∈ΔΓ) → y∉ $ ∈-ids-++⁺ʳ Γ ΔΓ′ y∈ΔΓ
... | [C-Split] {y}{Γ}{vcis} fresh-ys | refl =
  let
    (vs , cs , ys) = unzip₃ vcis
    Δ = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis
  in
  case ∈-ids-++⁻ Δ Γ y∈ of λ where
    (inj₂ y∈Γ) → y∉ y∈Γ
    (inj₁ y∈Δ) → L.All.lookup fresh-ys (x∈vcis⇒ {vcis = vcis} y∈Δ) (here refl)
-}

c∈⇒x∈ : ⟨ c , v ⟩at x ∈ᶜ Γ → x ∈ ids Γ
c∈⇒x∈ {Γ = ` _}             = λ{ (here ()); (there ()) }
c∈⇒x∈ {Γ = ⟨ _ , _ ⟩at _}   = λ{ (here refl) → here refl }
c∈⇒x∈ {Γ = ⟨ _ has _ ⟩at _} = λ{ (here ()); (there ()) }
c∈⇒x∈ {Γ = _ auth[ _ ]}     = λ{ (here ()); (there ()) }
c∈⇒x∈ {Γ = ⟨ _ ∶ _ ♯ _ ⟩}   = λ{ (here ()); (there ()) }
c∈⇒x∈ {Γ = _ ∶ _ ♯ _}       = λ{ (here ()); (there ()) }
c∈⇒x∈ {Γ = l ∣ r} = ∈ᶜ-++⁻ l r >≡>
  Sum.[ ∈-ids-++⁺ˡ l r ∘ c∈⇒x∈ {Γ = l}
      , ∈-ids-++⁺ʳ l r ∘ c∈⇒x∈ {Γ = r}
      ]

x∉⇒c∉ : x ∉ ids Γ → ⟨ c , v ⟩at x ∉ᶜ Γ
x∉⇒c∉ {Γ = Γ} = _∘ c∈⇒x∈ {Γ = Γ}

-- Collections on traces.
private variable X : Set ℓ

instance
  HX↠ₜ : ⦃ ∀ {αs} → (Γₜ —[ αs ]↠ₜ Γₜ′) has X ⦄ → (Γₜ —↠ₜ Γₜ′) has X
  HX↠ₜ .collect = collect ∘ proj₂

  HL↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Label
  HL↠ₜ {αs = αs} .collect _ = αs

  HA↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Ad
  HA↠ₜ .collect = concatMap authorizedHonAds ∘ allStates

  HN↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Name
  HN↠ₜ .collect = concatMap collect ∘ allStates

ads⊆ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γ ∈ allStates tr → advertisements Γ ⊆ advertisements tr
ads⊆ (_ ∎) (here refl) = L.Mem.∈-++⁺ˡ
ads⊆ (Γ —→⟨ _ ⟩ _ ⊢ tr) = λ where
  (here refl) → L.Mem.∈-++⁺ˡ
  (there Γ∈)  → L.Mem.∈-++⁺ʳ (advertisements Γ) ∘ ads⊆ tr Γ∈

labels : ∀ {X : Set} → ⦃ X has Label ⦄ → X → Labels
labels = collect

-- Well-founded recursion on smaller (i.e. prefix) traces.
instance
  MT : Measurable (Γₜ₀ —[ αs ]↠ₜ Γₜ″)
  MT {αs = αs} .∣_∣ _ = length αs

splitTraceˡ : (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr)
  → Γₜ₀ —[ take (toℕ $ L.Any.index xy∈) αs ]↠ₜ Γₜ
splitTraceˡ (_ —→⟨ _  ⟩ _ ⊢ _)  (here refl) = _ ∎ₜ
splitTraceˡ (_ —→⟨ Γ→ ⟩ p ⊢ Γ↠) (there Γ∈)  = _ —→ₜ⟨ Γ→ ⟩ p ⊢ splitTraceˡ Γ↠ Γ∈

≺-splitTraceˡ : (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr)
    → ∣ splitTraceˡ tr xy∈ ∣ ≺ ∣ tr ∣
≺-splitTraceˡ (_ —→⟨ _ ⟩ _ ⊢ _)   (here refl) = s≤s z≤n
≺-splitTraceˡ (_ —→⟨ _ ⟩ _ ⊢ tr′) (there Γ∈′) = s≤s (≺-splitTraceˡ tr′ Γ∈′)

_⊆ˢ_ : Γₜ —[ αs ]↠ₜ Γₜ′ → Δₜ —[ αs′ ]↠ₜ Δₜ′ → Set
tr ⊆ˢ tr′ = allStates tr ⊆ allStates tr′

⊆ˢ⇒names⊆ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) (tr′ : Δₜ —[ αs′ ]↠ₜ Δₜ′)
  → tr ⊆ˢ tr′
    --——————————————
  → tr ⊆⦅ names ⦆ tr′
⊆ˢ⇒names⊆ tr tr′ states⊆
  = ∈-concatMap⁺
  ∘ ⊆-resp-Any states⊆
  ∘ ∈-concatMap⁻ names

⊆ˢ⇒ads⊆ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) (tr′ : Δₜ —[ αs′ ]↠ₜ Δₜ′)
  → tr ⊆ˢ tr′
    --——————————————————————
  → tr ⊆⦅ advertisements ⦆ tr′
⊆ˢ⇒ads⊆ tr tr′ states⊆
  = ∈-concatMap⁺
  ∘ ⊆-resp-Any states⊆
  ∘ ∈-concatMap⁻ advertisements

⊆ˢ-splitTraceˡ : (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr)
  → splitTraceˡ tr xy∈ ⊆ˢ tr
⊆ˢ-splitTraceˡ tr xy∈ᵗ Γ∈ with tr | xy∈ᵗ | Γ∈
... | _ —→⟨ _ ⟩ _ ⊢ _  | here refl | here refl = here refl
... | _ —→⟨ _ ⟩ _ ⊢ _  | there _   | here refl = here refl
... | _ —→⟨ _ ⟩ _ ⊢ Γ↠ | there Γ∈′ | there x∈′ = there $ ⊆ˢ-splitTraceˡ Γ↠ Γ∈′ x∈′

_⊆ᵗʳ_ : Γₜ —[ αs ]↠ₜ Γₜ′ → Δₜ —[ αs′ ]↠ₜ Δₜ′ → Set
tr ⊆ᵗʳ tr′ = allTransitions tr ⊆ allTransitions tr′

⊆ᵗʳ-splitTraceˡ : (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr)
  → splitTraceˡ tr xy∈ ⊆ᵗʳ tr
⊆ᵗʳ-splitTraceˡ tr Γ∈ x∈ with tr | Γ∈ | x∈
... | _ —→⟨ _ ⟩ _ ⊢ _  | here refl | ()
... | _ —→⟨ _ ⟩ _ ⊢ _  | there _   | here refl = here refl
... | _ —→⟨ _ ⟩ _ ⊢ Γ↠ | there Γ∈′ | there x∈′ = there $ ⊆ᵗʳ-splitTraceˡ Γ↠ Γ∈′ x∈′

∃-weaken∈ : ∀ {P : Rel₀ Cfg} (tr : Γₜ —[ αs ]↠ₜ Γₜ′) (tr′ : Δₜ —[ αs′ ]↠ₜ Δₜ′)
  → tr ⊆ᵗʳ tr′
  → ∃[ tr ∋ P ]
    --——————————————————————————————
  → ∃[ tr′ ∋ P ]
∃-weaken∈ _ _ xs⊆ (x , x′ , y , y′ , xy∈ ,     xy≈ , H)
                 = x , x′ , y , y′ , xs⊆ xy∈ , xy≈ , H

∃-weakenP : ∀ {P Q : Rel₀ Cfg} (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → P ⇒² Q
  → ∃[ tr ∋ P ]
    --——————————————————————————————
  → ∃[ tr ∋ Q ]
∃-weakenP _ P⇒ (x , x′ , y , y′ , xy∈ , xy≈ , H)
              = x , x′ , y , y′ , xy∈ , xy≈ , P⇒ H

∃-splitTraceˡ : ∀ {X : Set} {P : X → Rel₀ Cfg} (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr) {x x′ : X}
  → P x ⇒² P x′
  → ∃[ splitTraceˡ tr xy∈ ∋ P x ]
    --——————————————————————————————
  → ∃[ tr                 ∋ P x′ ]
∃-splitTraceˡ tr xy∈ P⇒ = ∃-weakenP tr P⇒
                        ∘ ∃-weaken∈ (splitTraceˡ tr xy∈) tr (⊆ᵗʳ-splitTraceˡ tr xy∈)

∃-splitTraceˡ′ : ∀ {P Q : Rel₀ Cfg} (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr)
  → P ⇒² Q
  → ∃[ splitTraceˡ tr xy∈ ∋ P ]
    --——————————————————————————————
  → ∃[ tr                 ∋ Q ]
∃-splitTraceˡ′ tr xy∈ P⇒ = ∃-weakenP tr P⇒
                         ∘ ∃-weaken∈ (splitTraceˡ tr xy∈) tr (⊆ᵗʳ-splitTraceˡ tr xy∈)
