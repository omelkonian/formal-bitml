open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Lists
open import Prelude.General hiding (_⊢_)
open import Prelude.Nary
open import Prelude.Bifunctor
open import Prelude.SetCollections
open import Prelude.Measurable
open import Prelude.ToN
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Coercions
open import Prelude.Sets

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

-- ∈-deposits-

namesʳ⊆deposits :
    x ∈ˢ namesʳ g
  → Σ Participant λ A → Σ Value λ v →
      (A , v , x) ∈ˢ deposits g
namesʳ⊆deposits {x} {A :? v at x} (here refl) = A , v , here refl
namesʳ⊆deposits {x} {A :! v at x} (here refl) = A , v , here refl
namesʳ⊆deposits {x} {l ∣∣ r} x∈
  with ∈-∪⁻ _ (namesʳ l) (namesʳ r)
     $ mapMaybeˢ-∪ isInj₂ {names l}{names r} .proj₁ x∈
... | inj₁ x∈ˡ =
  let A , v , d∈ = namesʳ⊆deposits {g = l} x∈ˡ
  in A , v , ∈-∪⁺ˡ _ (deposits l) (deposits r) d∈
... | inj₂ x∈ʳ =
  let A , v , d∈ = namesʳ⊆deposits {g = r} x∈ʳ
  in A , v , ∈-∪⁺ʳ _ (deposits l) (deposits r) d∈

deposits⊆namesʳ :
    (A , v , x) ∈ˢ deposits Γ
  → x ∈ˢ namesʳ Γ
deposits⊆namesʳ {A} {v} {x} {⟨ A has v ⟩at x} (here refl) = here refl
deposits⊆namesʳ {A} {v} {x} {l ∣ r} d∈
  with ∈-deposits-∪⁻ l r d∈
... | inj₁ d∈ˡ =
  ∈-ids-∪⁺ˡ l r $ deposits⊆namesʳ {Γ = l} d∈ˡ
... | inj₂ d∈ʳ =
  ∈-ids-∪⁺ʳ l r $ deposits⊆namesʳ {Γ = r} d∈ʳ

deposits⊆⇒namesʳ⊆ :
    deposits ad ⊆ˢ deposits Γ
  → namesʳ ad ⊆ˢ namesʳ Γ
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
      x ∉ˢ ids Γ
    → ⟨ [ d ] , v ⟩at x ∣ Γ —[ α ]→ Γ′
    → cv α ≡ just x
      --—————————————————————————————————
    → x ∉ˢ ids Γ′
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

c⇒x : ∀ {Γ : BaseCfg} → ⌞ ⟨ c , v ⟩at x ⌟ ≡ Γ → inj₂ x ∈ˢ names Γ
c⇒x refl = here refl

c∈⇒x∈ : ∀ Γ →
  ⟨ c , v ⟩at x ∈ᶜ Γ
  ──────────────────
  x ∈ˢ ids Γ
c∈⇒x∈ Γ = flip (∈ˢ-mapMaybe⁺ isInj₂ {xs = names Γ}) refl
        ∘ collectFromBase⁺ {Γ = Γ}
        ∘ L.Any.map c⇒x
        ∘ ∈-Cfg′ _ Γ

x∉⇒c∉ : x ∉ˢ ids Γ → ⟨ c , v ⟩at x ∉ᶜ Γ
x∉⇒c∉ {Γ = Γ} = _∘ c∈⇒x∈ Γ

{-
module _ {c}{v}{x} where

  postulate
    c∈⇒x∈∘∈ᶜ-++⁺ˡ : (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ)
      --————————————————————————
      → ( c∈⇒x∈ (Γ ∣ Γ′)
        ∘ ∈ᶜ-++⁺ˡ Γ Γ′
        ) c∈
      ≡ ( ∈-ids-++⁺ˡ Γ Γ′
        ∘ c∈⇒x∈ Γ
        ) c∈
  -- c∈⇒x∈∘∈ᶜ-++⁺ˡ {Γ = Γ}{Γ′} c∈
  --   rewrite cfgToList-++ Γ Γ′
  --   = {!!}

    c∈⇒x∈∘∈ᶜ-++⁺ʳ : (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ′)
      --————————————————————————
      → ( c∈⇒x∈ (Γ ∣ Γ′)
        ∘ ∈ᶜ-++⁺ʳ Γ Γ′
        ) c∈
      ≡ ( ∈-ids-++⁺ʳ Γ Γ′
        ∘ c∈⇒x∈ Γ′
        ) c∈

  open L.Perm

  open import Prelude.Lists.PermutationsMeta
  ∈-resp-↭∘c∈⇒x∈ : ∀ Γ Γ′
    → (Γ≈ : Γ ≈ Γ′)
    → (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ)
      --————————————————————————————————————
    → ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) -- x ∈ ids Γ′
      ∘ c∈⇒x∈ Γ                         -- x ∈ ids Γ
      ) c∈                              -- ⟨ c , v ⟩ₓ ∈ Γ
    ≡ ( c∈⇒x∈ Γ′             -- x ∈ ids Γ′
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈ -- ⟨ c , v ⟩ₓ ∈ Γ′
      ) c∈                   -- ⟨ c , v ⟩ₓ ∈ Γ
  ∈-resp-↭∘c∈⇒x∈ Γ Γ′ Γ≈ c∈ =
    begin≡
      ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈)
      ∘ c∈⇒x∈ Γ
      ) c∈
    ≡⟨⟩
      ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) -- x ∈ ids Γ′
      ∘ flip (∈-mapMaybe⁺ isInj₂) refl  -- x ∈ ids Γ
      ∘ ∈-concatMap⁺                    -- inj₂ x ∈ names Γ
      ∘ L.Any.map c⇒x                   -- Any (λ ◆ → inj₂ x ∈ names ◆) Γ
      ∘ ∈-Cfg′ _ Γ                      -- `⟨ c , v ⟩ₓ ∈ toList Γ
      ) c∈                              -- ⟨ c , v ⟩ₓ ∈ᶜ Γ
    ≡⟨ ∈-resp-↭∘∈-mapMaybe⁺ isInj₂ (≈⇒names↭ {Γ}{Γ′} Γ≈) refl _ ⟩
      ( flip (∈-mapMaybe⁺ isInj₂) refl -- x ∈ ids Γ′
      ∘ ∈-resp-↭ (≈⇒names↭ {Γ}{Γ′} Γ≈) -- inj₂ x ∈ names Γ′
      ∘ ∈-concatMap⁺                   -- inj₂ x ∈ names Γ
      ∘ L.Any.map c⇒x                  -- Any (λ ◆ → inj₂ x ∈ names ◆) Γ
      ∘ ∈-Cfg′ _ Γ                     -- `⟨ c , v ⟩ₓ ∈ toList Γ
      ) c∈                             -- ⟨ c , v ⟩ₓ ∈ᶜ Γ
    ≡⟨ cong (flip (∈-mapMaybe⁺ isInj₂) refl)
            (∈-resp-↭∘∈-concatMap⁺ Γ≈ _)  ⟩
      ( flip (∈-mapMaybe⁺ isInj₂) refl -- x ∈ ids Γ′
      ∘ ∈-concatMap⁺                   -- inj₂ x ∈ names Γ′
      ∘ Any-resp-↭ Γ≈                  -- Any (λ ◆ → inj₂ x ∈ names ◆) Γ′
      ∘ L.Any.map c⇒x                  -- Any (λ ◆ → inj₂ x ∈ names ◆) Γ
      ∘ ∈-Cfg′ _ Γ                     -- `⟨ c , v ⟩ₓ ∈ toList Γ
      ) c∈                             -- ⟨ c , v ⟩ₓ ∈ᶜ Γ
    ≡⟨ cong (flip (∈-mapMaybe⁺ isInj₂) refl ∘ ∈-concatMap⁺)
            (Any-resp-↭∘Any-map c⇒x Γ≈ _) ⟩
      ( flip (∈-mapMaybe⁺ isInj₂) refl -- x ∈ ids Γ′
      ∘ ∈-concatMap⁺                   -- inj₂ x ∈ names Γ′
      ∘ L.Any.map c⇒x                  -- Any (λ ◆ → inj₂ x ∈ names ◆) Γ′
      ∘ ∈-resp-↭ Γ≈                    -- `⟨ c , v ⟩ₓ ∈ toList Γ′
      ∘ ∈-Cfg′ _ Γ                     -- `⟨ c , v ⟩ₓ ∈ toList Γ
      ) c∈                             -- ⟨ c , v ⟩ₓ ∈ᶜ Γ
    ≡⟨ sym $ cong (flip (∈-mapMaybe⁺ isInj₂) refl ∘ ∈-concatMap⁺ ∘ L.Any.map c⇒x)
           $ ∈-resp-↭∘∈-Cfg′ (⟨ c , v ⟩at x) Γ Γ′ Γ≈ c∈ ⟩
      ( flip (∈-mapMaybe⁺ isInj₂) refl -- x ∈ ids Γ′
      ∘ ∈-concatMap⁺                   -- inj₂ x ∈ names Γ′
      ∘ L.Any.map c⇒x                  -- Any (λ ◆ → inj₂ x ∈ names ◆) Γ′
      ∘ ∈-Cfg′ _ Γ′                    -- `⟨ c , v ⟩ₓ ∈ toList Γ′
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈           -- ⟨ c , v ⟩ₓ ∈ toList Γ′
      ) c∈                             -- ⟨ c , v ⟩ₓ ∈ᶜ Γ
    ≡⟨⟩
      ( c∈⇒x∈ Γ′
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈
      ) c∈
    ∎≡ where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

  ∈ᶜ-resp-≈∘∈ᶜ-resp-≈ : ∀ Γ Γ′
    → (Γ≈ : Γ ≈ Γ′)
    → (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ)
      --————————————————————————————————————
    → ( ∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈)
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈
      ) c∈
    ≡ c∈
  ∈ᶜ-resp-≈∘∈ᶜ-resp-≈ _ _ = ∈-map-resp-↭∘∈-map-resp-↭˘ to[ Cfg ]

  ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈ : ∀ Γ Γ′ (Γ≈ : Γ ≈ Γ′)
    → (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ)
      --———————————————————————————————————————
    → ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ} (↭-sym Γ≈))
      ∘ c∈⇒x∈ Γ′
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈
      ) c∈
    ≡ c∈⇒x∈ Γ c∈
  {- i.e. the following diagram commutes

      ids Γ ←————— ↭ ————— ids Γ′
        ↑                    ↑
        ∥                    ∣
        ∥                    ∣
      c∈⇒x∈                c∈⇒x∈
        ∥                    ∣
        ∥                    ∣
        Γ ———————— ≈ ——————→ Γ′
  -}
  ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈ Γ Γ′ Γ≈ c∈ =
    begin≡
      ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ} (↭-sym Γ≈))
      ∘ c∈⇒x∈ Γ′
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈
      ) c∈
    ≡⟨ ∈-resp-↭∘c∈⇒x∈ Γ′ Γ (↭-sym Γ≈) (∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈ c∈) ⟩
      ( c∈⇒x∈ Γ
      ∘ ∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈)
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈
      ) c∈
    ≡⟨ cong (c∈⇒x∈ Γ) $ ∈-map-resp-↭∘∈-map-resp-↭˘ to[ Cfg ] Γ≈ c∈ ⟩
      c∈⇒x∈ Γ c∈
    ∎≡ where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

  ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈˘ : ∀ Γ Γ′ (Γ≈ : Γ′ ≈ Γ)
    → (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ)
      --———————————————————————————————————————
    → ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ} Γ≈)
      ∘ c∈⇒x∈ Γ′
      ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} (↭-sym Γ≈)
      ) c∈
    ≡ c∈⇒x∈ Γ c∈
  ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈˘ Γ Γ′ Γ≈
    with go ← ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈ Γ Γ′ (↭-sym Γ≈)
    rewrite L.Perm.↭-sym-involutive Γ≈
    = go
-}

-- Collections on traces.
private variable X : Set ℓ

instance
  HX↠ₜ : ⦃ _ : DecEq X ⦄ → ⦃ ∀ {αs} → (Γₜ —[ αs ]↠ₜ Γₜ′) has X ⦄ → (Γₜ —↠ₜ Γₜ′) has X
  HX↠ₜ .collect = collect ∘ proj₂

  HL↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Label
  HL↠ₜ {αs = αs} .collect _ = fromList αs

  HA↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Ad
  HA↠ₜ .collect = concatMapˢ authorizedHonAds ∘ fromList ∘ allStates

  HN↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Name
  HN↠ₜ .collect = concatMapˢ collect ∘ fromList ∘ allStates

ads⊆ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γ ∈ allStates tr → Γ ⊆⦅ advertisements ⦆ tr
ads⊆ tr Γ∈ ad∈
  = ∈ˢ-concat⁺ {xss = mapˢ authorizedHonAds (fromList (allStates tr))}
  $ L.Any.map (λ where refl → ad∈)
  $ ∈ˢ-map⁺ authorizedHonAds {xs = fromList (allStates tr)} $ ∈ˢ-fromList⁺ Γ∈

labels : ∀ {X : Set} → ⦃ X has Label ⦄ → X → Set⟨ Label ⟩
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

_⊆ˢᵗ_ : Γₜ —[ αs ]↠ₜ Γₜ′ → Δₜ —[ αs′ ]↠ₜ Δₜ′ → Set
tr ⊆ˢᵗ tr′ = allStates tr ⊆ allStates tr′

⊆ˢᵗ⇒names⊆ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) (tr′ : Δₜ —[ αs′ ]↠ₜ Δₜ′) →
  tr ⊆ˢᵗ tr′
  ────────────────────────
  tr ⊆⦅ names ⦆ tr′
⊆ˢᵗ⇒names⊆ tr tr′ states⊆
  = ∈ˢ-concatMap⁺ names {fromList (allStates tr′)}
  ∘ Anyˢ-fromList⁺
  ∘ ⊆-resp-Any states⊆
  ∘ Anyˢ-fromList⁻
  ∘ ∈ˢ-concatMap⁻ names {fromList (allStates tr)}

⊆ˢᵗ⇒ads⊆ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) (tr′ : Δₜ —[ αs′ ]↠ₜ Δₜ′)
  → tr ⊆ˢᵗ tr′
    --——————————————————————
  → tr ⊆⦅ advertisements ⦆ tr′
⊆ˢᵗ⇒ads⊆ tr tr′ states⊆
  = ∈ˢ-concatMap⁺ advertisements {fromList (allStates tr′)}
  ∘ Anyˢ-fromList⁺
  ∘ ⊆-resp-Any states⊆
  ∘ Anyˢ-fromList⁻
  ∘ ∈ˢ-concatMap⁻ advertisements  {fromList (allStates tr)}

⊆ˢᵗ-splitTraceˡ : (tr : Γₜ₀ —[ αs ]↠ₜ Γₜ″) (xy∈ : (Γₜ , Γₜ′) ∈ allTransitionsᵗ tr)
  → splitTraceˡ tr xy∈ ⊆ˢᵗ tr
⊆ˢᵗ-splitTraceˡ tr xy∈ᵗ Γ∈ with tr | xy∈ᵗ | Γ∈
... | _ —→⟨ _ ⟩ _ ⊢ _  | here refl | here refl = here refl
... | _ —→⟨ _ ⟩ _ ⊢ _  | there _   | here refl = here refl
... | _ —→⟨ _ ⟩ _ ⊢ Γ↠ | there Γ∈′ | there x∈′ = there $ ⊆ˢᵗ-splitTraceˡ Γ↠ Γ∈′ x∈′

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
