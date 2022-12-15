open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Prelude.Bifunctor
open import Prelude.Nary hiding (⟦_⟧)
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.General hiding (_⊢_)
open import Prelude.ToN
open import Prelude.Traces
open import Prelude.InferenceRules

module BitML.Properties.Lifetime
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Predicate
open import BitML.Contracts Participant Honest hiding (d)
open import BitML.Semantics Participant Honest
open import BitML.Properties.Helpers Participant Honest

data _↝_ : Rel₀ Contracts where

  put↝ : ∀ {i : Index c} → let open ∣SELECT c i in

    d∗ ≡ put xs &reveal as if p ⇒ c′
    ────────────────────────────────────
    c ↝ c′

  split↝ : ∀ {i : Index c} → let open ∣SELECT c i in

    ∙ d∗ ≡ split vcs
    ∙ c′ ∈ map proj₂ vcs
      ────────────────────────────────────
      c ↝ c′

private variable X : Set ℓ

weaken‼ : ∀ {xs ys : List X} → xs ⊆ ys → Index xs → Index ys
weaken‼ {xs = x ∷ xs} xs⊆ 0F = L.Any.index $ xs⊆ (here refl)
weaken‼ {xs = _ ∷ xs} xs⊆ (fsuc i) = weaken‼ (xs⊆ ∘ there) i

weaken‼′ : ∀ {xs ys : List X} {i : Index xs} (xs⊆ : xs ⊆ ys) →
  (xs ‼ i) ≡ (ys ‼ weaken‼ xs⊆ i)
weaken‼′ {xs = x ∷ xs} {ys} {i = 0F} xs⊆ = L.Any.lookup-index {xs = ys} (xs⊆ (here refl))
weaken‼′ {xs = _ ∷ xs} {i = fsuc i} xs⊆ = weaken‼′ (xs⊆ ∘ there)

weaken↝ : c ⊆ c′ → c ↝ c″ → c′ ↝ c″
weaken↝ c⊆ (put↝ {i = i} d≡) rewrite weaken‼′ {i = i} c⊆ = put↝ d≡
weaken↝ c⊆ (split↝ {i = i} d≡ c∈) rewrite weaken‼′ {i = i} c⊆ = split↝ d≡ c∈

weaken∈ : ∀ {i : Index c} → let open ∣SELECT c i in
  d ∈ c → [ d∗ ] ↝ c′ → c ↝ c′
weaken∈ {c} d∈ (put↝ {i = 0F} d≡)
  rewrite L.Any.lookup-index {xs = c} d∈
        | removeTopDecorations-idemp (c ‼ L.Any.index d∈)
  = put↝ d≡
weaken∈ {c} d∈ (split↝ {i = 0F} d≡ c∈)
  rewrite L.Any.lookup-index {xs = c} d∈
        | removeTopDecorations-idemp (c ‼ L.Any.index d∈)
  = split↝ d≡ c∈


data _↝∗_ : Rel₀ Contracts where
  base : c ↝∗ c
  step : c ↝ c′ → c′ ↝∗ c″ → c ↝∗ c″

step˘ : c ↝∗ c′ → c′ ↝ c″ → c ↝∗ c″
step˘ base = flip step base
step˘ (step c↝ c↝∗) c↝′ = step c↝ (step˘ c↝∗ c↝′)

_∙↝∗_ : Ad → Contracts → Set
(⟨ _ ⟩ c) ∙↝∗ c′ = c ↝∗ c′

step∙˘ : ad ∙↝∗ c → c ↝ c′ → ad ∙↝∗ c′
step∙˘ = step˘

open ⊆-Reasoning Contract renaming (begin_ to begin⊆_; _∎ to _⊆∎)

h-sub↝ : c ↝ c′ → subtermsᶜ′ c′ ⊆ subtermsᶜ′ c
h-sub↝ (put↝ {c}{xs}{as}{p}{c′}{i} d≡) = let open ∣SELECT c i in
  begin⊆ subtermsᶜ′ c′ ≡˘⟨ cong subtermsᵈ′ d≡ ⟩
         subtermsᵈ′ d∗ ⊆⟨ h-sub‼ {c} ⟩
         subtermsᶜ′ c  ⊆∎
h-sub↝ (split↝ {c}{vcs}{c′}{i} d≡ c∈) = let open ∣SELECT c i in
  begin⊆ subtermsᶜ′ c′ ⊆⟨ subterms⊆ᵛᶜˢ′ {c′}{vcs} c∈ ⟩
         subtermsᵈ′ (split vcs) ≡˘⟨ cong subtermsᵈ′ d≡ ⟩
         subtermsᵈ′ d∗ ⊆⟨  h-sub‼ {c} ⟩
         subtermsᶜ′ c  ⊆∎

h-sub↝∗ : c ↝∗ c′ → subtermsᶜ′ c′ ⊆ subtermsᶜ′ c
h-sub↝∗ base = id
h-sub↝∗ (step c↝ c↝∗) = h-sub↝ c↝ ∘ h-sub↝∗ c↝∗

h-sub∙↝∗ : ad ∙↝∗ c → c ⊆ subtermsᵃ′ ad
h-sub∙↝∗ ad↝ = h-sub↝∗ ad↝ ∘ subterms⊆ᶜˢ
