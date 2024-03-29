open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.General hiding (_⊢_)
open import Prelude.ToN
open import Prelude.Traces
open import Prelude.InferenceRules

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Properties.Lifetime (⋯ : ⋯) where

open import BitML.Contracts ⋯ hiding (d)
open import BitML.Semantics ⋯
open import BitML.Properties.Helpers ⋯

data _↝_ : Rel₀ Contract where

  put↝ : ∀ {i : Index c} → let open ∣SELECT c i in

    d∗ ≡ put xs &reveal as if p ⇒ c′
    ────────────────────────────────────
    c ↝ c′

  split↝ : ∀ {i : Index c} → let open ∣SELECT c i in

    ∙ d∗ ≡ split vcs
    ∙ c′ ∈ map proj₂ vcs
      ────────────────────────────────────
      c ↝ c′

private variable X : Type ℓ

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


data _↝∗_ : Rel₀ Contract where
  base : c ↝∗ c
  step : c ↝ c′ → c′ ↝∗ c″ → c ↝∗ c″

step˘ : c ↝∗ c′ → c′ ↝ c″ → c ↝∗ c″
step˘ base = flip step base
step˘ (step c↝ c↝∗) c↝′ = step c↝ (step˘ c↝∗ c↝′)

_∙↝∗_ : Ad → Contract → Type
(⟨ _ ⟩ c) ∙↝∗ c′ = c ↝∗ c′

step∙˘ : ad ∙↝∗ c → c ↝ c′ → ad ∙↝∗ c′
step∙˘ = step˘

h-sub↝ : c ↝ c′ → subterms c′ ⊆ subterms c
h-sub↝ = λ where
  (put↝ {c}{xs}{as}{p}{c′}{i} d≡) → let open ∣SELECT c i in
    begin⊆ subterms c′ ≡˘⟨ cong subterms d≡ ⟩
           subterms d∗ ⊆⟨ h-sub‼ {c} ⟩
           subterms c  ⊆∎
  (split↝ {c}{vcs}{c′}{i} d≡ c∈)  → let open ∣SELECT c i in
    begin⊆ subterms c′          ⊆⟨ subterms⊆ᵛ′ {c′}{vcs} c∈ ⟩
           subterms (split vcs) ≡˘⟨ cong subterms d≡ ⟩
           subterms d∗          ⊆⟨  h-sub‼ {c} ⟩
           subterms c           ⊆∎
 where open ⊆-Reasoning Branch renaming (begin_ to begin⊆_; _∎ to _⊆∎)

h-sub↝∗ : c ↝∗ c′ → subterms c′ ⊆ subterms c
h-sub↝∗ base = id
h-sub↝∗ (step c↝ c↝∗) = h-sub↝ c↝ ∘ h-sub↝∗ c↝∗

h-sub∙↝∗ : ad ∙↝∗ c → c ⊆ subterms ad
h-sub∙↝∗ ad↝ = h-sub↝∗ ad↝ ∘ subterms⊆ᶜ
