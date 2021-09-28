open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.ToList
open import Prelude.Lists
open import Prelude.General hiding (_⊢_)

module BitML.Properties.Helpers
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest

≈ᵗ-refl : Γₜ ≈ Γₜ
≈ᵗ-refl = refl , ↭-refl

allStatesᵗ⁺ : (Γₜ —[ αs ]↠ₜ Γₜ′) → List⁺ Cfgᵗ
allStatesᵗ⁺ = λ where
  (tc ∎)              → tc ∷ []
  (tc —→⟨ _ ⟩ _ ⊢ tr) → tc ∷⁺ allStatesᵗ⁺ tr

allStates∈ : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γₜ ∈ allStatesᵗ⁺ tr
allStates∈ = λ where
  (_ ∎)             → here refl
  (_ —→⟨ _ ⟩ _ ⊢ _) → here refl

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

allStatesᵗ : (Γₜ —[ αs ]↠ₜ Γₜ′) → List Cfgᵗ
allStatesᵗ = toList ∘ allStatesᵗ⁺

allStates⁺ : (Γₜ —[ αs ]↠ₜ Γₜ′) → List⁺ Cfg
allStates⁺ = L.NE.map cfg ∘ allStatesᵗ⁺

allStates : (Γₜ —[ αs ]↠ₜ Γₜ′) → List Cfg
allStates = toList ∘ allStates⁺

_~[_]→ₜ_ : Cfgᵗ → Label → Cfgᵗ → Set
x ~[ α ]→ₜ y =
  ∃ λ x′ → ∃ λ y′ →
      (x ≈ x′ × y ≈ y′)
    × (x′ —[ α ]→ₜ y′)

zoom :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → α ∈ αs
    --———————————————————————————————————
  → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
        (x ∈ allStatesᵗ tr)
      × (y ∈ allStatesᵗ tr)
      × (x ≈ x′ × y ≈ y′)
      × (x′ —[ α ]→ₜ y′)
zoom (_—→⟨_⟩_⊢_ x {x′}{y}{y′} Γ→ eq Γ↠) (here refl)
  rewrite allStatesᵗ⁺-∷ {Γₜ = x} Γ→ eq Γ↠
  = -, -, -, -, here refl , there (allStates∈ Γ↠) , eq , Γ→
zoom (_ —→⟨ _ ⟩ _ ⊢ Γ↠) (there α∈)
  with _ , _ , _ , _ , x∈ , y∈ , ≈Γ→ ← zoom Γ↠ α∈
    = -, -, -, -, there x∈ , there y∈ , ≈Γ→

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
