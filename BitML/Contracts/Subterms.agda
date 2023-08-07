------------------------------------------------------------------------
-- Collecting subterms for contracts, preconditions and advertisments.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Lists
open import Prelude.Lists.Collections
open import Prelude.Validity

open import BitML.BasicTypes

module BitML.Contracts.Subterms ⋯ (let open ⋯ ⋯) where

open import BitML.Contracts.Types ⋯ hiding (C)
open import BitML.Contracts.Collections ⋯
open import BitML.Contracts.Induction ⋯
open import BitML.Contracts.Validity ⋯

subtermsℂ subtermsℂ⁺ subtermsℂ′ : ℂ → List Branch
subtermsℂ c@(D _)   = drop 1 $ subtermsℂ⁺ c
subtermsℂ c@(C _)   = subtermsℂ⁺ c
subtermsℂ c@(VCS _) = subtermsℂ⁺ c

subterms subterms⁺ subterms′ : ∀ {X} → ⦃ Toℂ X ⦄ → X → List Branch
subterms  = subtermsℂ  ∘ toℂ
subterms⁺ = subtermsℂ⁺ ∘ toℂ
subterms′ = subtermsℂ′ ∘ toℂ

subtermsℂ⁺ = mkCollect go
  where
    go : ∀ d → (∀ d′ → d′ ≺ D d → Contract) → Contract
    go d f with d
    ... | _       ∶ d              = f (D d) ≺-auth -- it
    ... | after _ ∶ d              = f (D d) ≺-after -- it
    ... | split vcs                = d ∷ f (VCS vcs) ≺-split -- it
    ... | put _ &reveal _ if _ ⇒ c = d ∷ f (C c) ≺-put -- it
    ... | withdraw _               = d ∷ []

subtermsℂ′ (D d) with d
... | _       ∶ d              = subtermsℂ′ (D d)
... | after _ ∶ d              = subtermsℂ′ (D d)
... | split vcs                = subtermsℂ′ (VCS vcs)
... | put _ &reveal _ if _ ⇒ c = subtermsℂ′ (C c)
... | withdraw _               = []
subtermsℂ′ (C [])                = []
subtermsℂ′ (C (d ∷ c))           = d ∷ subtermsℂ′ (D d) ++ subtermsℂ′ (C c)
subtermsℂ′ (VCS [])              = []
subtermsℂ′ (VCS ((_ , c) ∷ vcs)) = subtermsℂ′ (C c) ++ subtermsℂ′ (VCS vcs)

{-
_ = subtermsᵈ⁺ (put xs &reveal as if p ⇒ c)
  ≡ (put xs &reveal as if p ⇒ c) ∷ subtermsᶜ⁺ c
  ∋ refl
_ = subtermsᵈ⁺ (A ∶ d) ≡ subtermsᵈ⁺ d
  ∋ refl
_ = subtermsᵈ⁺ (split vcs) ≡ split vcs ∷ subtermsᵛ⁺ vcs
  ∋ refl

subterms⊆ : ∀ 𝕔 → subtermsℂ⁺ 𝕔 ⊆ subtermsℂ′ 𝕔
subterms⊆∗ : removeTopDecorations d ∈ subtermsᶜ′ [ removeTopDecorations d ]
mutual
  subterms⁺⊆ᵈ′ : subtermsᵈ⁺ d ⊆ removeTopDecorations d ∷ subtermsᵈ′ d
  subterms⁺⊆ᶜ′ : subtermsᶜ⁺ c ⊆ subtermsᶜ′ c
  subterms⁺⊆ᵛ′ : subtermsᵛ⁺ vcs ⊆ subtermsᵛ′ vcs
-}

h-subᵈ :
    d ∈ subterms′ d′
    --------------------------------------
  → removeTopDecorations d ∈ subterms⁺ d′

h-subᶜ :
    d ∈ subterms′ ds
    --------------------------------------
  → removeTopDecorations d ∈ subterms⁺ ds

h-subᵛ :
    d ∈ subterms′ vcs
    --------------------------------------
  → removeTopDecorations d ∈ subterms⁺ vcs

h-subᵈ {d} {put _ &reveal _ if _ ⇒ cs} d∈ = there $ h-subᶜ {ds = cs} d∈
h-subᵈ {d} {split vcs}                 d∈ = there $ h-subᵛ {vcs = vcs} d∈
h-subᵈ {d} {_       ∶ d′} d∈ = h-subᵈ {d′ = d′} d∈
h-subᵈ {d} {after _ ∶ d′} d∈ = h-subᵈ {d′ = d′} d∈

h-subᶜ {.d} {d ∷ ds} (here refl)
  with d
... | put _ &reveal _ if _ ⇒ _ = here refl
... | withdraw _               = here refl
... | split _                  = here refl
... | _       ∶ d′ = h-subᶜ {ds = d′ ∷ ds} (here refl)
... | after _ ∶ d′ = h-subᶜ {ds = d′ ∷ ds} (here refl)
h-subᶜ {d} {d′ ∷ ds} (there d∈)
  with ∈-++⁻ (subterms′ d′) d∈
... | inj₂ d∈ʳ = ∈-++⁺ʳ (subterms⁺ d′) (h-subᶜ {ds = ds} d∈ʳ)
... | inj₁ d∈ˡ
  with d′ | d∈ˡ
... | put _ &reveal _ if _ ⇒ cs | d∈ˡ′ = there $ ∈-++⁺ˡ $ h-subᶜ {ds = cs} d∈ˡ′
... | split vcs                 | d∈ˡ′ = there $ ∈-++⁺ˡ $ h-subᵛ {vcs = vcs} d∈ˡ′
... | _       ∶ d″ | d∈ˡ′ = ∈-++⁺ˡ $ h-subᵈ {d′ = d″} d∈ˡ′
... | after _ ∶ d″ | d∈ˡ′ = ∈-++⁺ˡ $ h-subᵈ {d′ = d″} d∈ˡ′

h-subᵛ {d} {(_ , cs) ∷ vcs} d∈
  with ∈-++⁻ (subterms′ cs) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ $ h-subᶜ {ds = cs} d∈ˡ
... | inj₂ d∈ʳ = ∈-++⁺ʳ (subterms⁺ cs) $ h-subᵛ {vcs = vcs} d∈ʳ

h-sub∗ : subterms′ (removeTopDecorations d) ⊆ subterms′ d
h-sub∗ {_ ∶ d} = h-sub∗ {d}
h-sub∗ {after _ ∶ d} = h-sub∗ {d}
h-sub∗ {put _ &reveal _ if _ ⇒ _} = id
h-sub∗ {withdraw _} = id
h-sub∗ {split _} = id

h-sub‼ : ∀ {i : Index c} → subterms′ (removeTopDecorations $ c ‼ i) ⊆ subterms′ c
h-sub‼ {d ∷ _} {0F}     = there ∘ ∈-++⁺ˡ               ∘ h-sub∗ {d}
h-sub‼ {d ∷ c} {fsuc i} = there ∘ ∈-++⁺ʳ (subterms′ d) ∘ h-sub‼ {c}{i}

-- Lemmas about `subterms`

↦-∈ : ∀ {R : Branch → Type}
  → (∀ {d} → d ∈ ds → subterms⁺ d ↦′ R)
  → subterms⁺ ds ↦′ R
↦-∈ {ds = d ∷ ds} f x∈
  with ∈-++⁻ (subterms⁺ d) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ (f ∘ there) x∈ʳ

↦-∈ᵛ : ∀ {R : Branch → Type}
  → (∀ {c} → c ∈ map proj₂ vcs → subterms⁺ c ↦′ R)
  → subterms⁺ vcs ↦′ R
↦-∈ᵛ {vcs = (_ , c) ∷ vcs} f x∈
  with ∈-++⁻ (subterms⁺ c) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ᵛ (f ∘ there) x∈ʳ

mutual
  subterms⊆ᶜ : ds ⊆ subterms′ ds
  subterms⊆ᶜ {ds = d ∷ ds} (here refl) = here refl
  subterms⊆ᶜ {ds = d ∷ ds} (there d∈)  = there $ ∈-++⁺ʳ (subterms′ d) (subterms⊆ᶜ d∈)

  subterms⊆ᵛ : (v , c) ∈ vcs → c ⊆ subterms′ vcs
  subterms⊆ᵛ {vcs = (_ , c) ∷ vcs} (here refl) = ∈-++⁺ˡ ∘ subterms⊆ᶜ
  subterms⊆ᵛ {vcs = (_ , c) ∷ vcs} (there p)   = ∈-++⁺ʳ (subterms′ c) ∘ subterms⊆ᵛ p

  subterms⊆ᵛ′ : c ∈ map proj₂ vcs → subterms′ c ⊆ subterms′ (split vcs)
  subterms⊆ᵛ′ {vcs = (v , c) ∷ _}   (here refl) = ∈-++⁺ˡ
  subterms⊆ᵛ′ {vcs = (v , c) ∷ vcs} (there c∈)  = ∈-++⁺ʳ _ ∘ subterms⊆ᵛ′ {vcs = vcs} c∈

  subterms⊆ᵛᶜⁱˢ : ∀ {vcis : List (Value × Contract × Id)} → let (vs , cs , ys) = unzip₃ vcis in
      c ∈ cs
    → subterms′ c ⊆ subterms′ (split $ zip vs cs)
  subterms⊆ᵛᶜⁱˢ {vcis = (v , c , _) ∷ _}    (here refl)
    = ∈-++⁺ˡ
  subterms⊆ᵛᶜⁱˢ {vcis = (v , c , _) ∷ vcis} (there c∈)
    = ∈-++⁺ʳ _ ∘ subterms⊆ᵛᶜⁱˢ {vcis = vcis} c∈

mutual
  subterms′-names⊆ᵈ : d ∈ subterms′ d′ → names d ⊆ names d′
  subterms′-names⊆ᵈ {d′ = d} with d
  ... | put xs &reveal as if _ ⇒ ds = λ x∈ → ∈-++⁺ʳ (map inj₂ xs) ∘ ∈-++⁺ʳ (map inj₁ as) ∘ subterms′-names⊆ᶜ {ds = ds} x∈
  ... | withdraw _                  = λ ()
  ... | split vcs                   = subterms′-names⊆ᵛ {vcs = vcs}
  ... | _ ∶ d′                      = subterms′-names⊆ᵈ {d′ = d′}
  ... | after _ ∶ d′                = subterms′-names⊆ᵈ {d′ = d′}

  subterms′-names⊆ᶜ : d ∈ subterms′ ds → names d ⊆ names ds
  subterms′-names⊆ᶜ {ds = d ∷ ds} (here refl) = ∈-++⁺ˡ
  subterms′-names⊆ᶜ {ds = d ∷ ds} (there p)
    with ∈-++⁻ _ p
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᶜ {ds = ds} p′
  ... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-names⊆ᵈ {d′ = d} p′

  subterms′-names⊆ᵛ : d ∈ subterms′ vcs → names d ⊆ names vcs
  subterms′-names⊆ᵛ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᵛ {vcs = vcs} p
  subterms′-names⊆ᵛ {vcs = (_ , ds) ∷ vcs} p
    with ∈-++⁻ (subterms′ ds) p
  ... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-names⊆ᶜ {ds = ds} p′
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-names⊆ᵛ {vcs = vcs} p′

mutual
  subterms′-putComponents⊆ᵈ : d ∈ subterms′ d′ → putComponents d ⊆ putComponents d′
  subterms′-putComponents⊆ᵈ {d′ = d} with d
  ... | put _ &reveal _ if _ ⇒ ds = λ x∈ → there ∘ subterms′-putComponents⊆ᶜ {ds = ds} x∈
  ... | withdraw _                = λ ()
  ... | split vcs                 = subterms′-putComponents⊆ᵛ {vcs = vcs}
  ... | _ ∶ d′                    = subterms′-putComponents⊆ᵈ {d′ = d′}
  ... | after _ ∶ d′              = subterms′-putComponents⊆ᵈ {d′ = d′}

  subterms′-putComponents⊆ᶜ : d ∈ subterms′ ds → putComponents d ⊆ putComponents ds
  subterms′-putComponents⊆ᶜ {ds = _ ∷ _}  (here refl) = ∈-++⁺ˡ
  subterms′-putComponents⊆ᶜ {ds = d ∷ ds} (there p)
    with ∈-++⁻ _ p
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᶜ {ds = ds} p′
  ... | inj₁ p′ = ∈-++⁺ˡ   ∘ subterms′-putComponents⊆ᵈ  {d′ = d} p′

  subterms′-putComponents⊆ᵛ : d ∈ subterms′ vcs → putComponents d ⊆ putComponents vcs
  subterms′-putComponents⊆ᵛ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᵛ {vcs = vcs} p
  subterms′-putComponents⊆ᵛ {vcs = (_ , ds) ∷ vcs} p
    with ∈-++⁻ (subterms′ ds) p
  ... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms′-putComponents⊆ᶜ {ds = ds} p′
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-putComponents⊆ᵛ {vcs = vcs} p′

mutual
  subterms′-part⊆ᵈ : d ∈ subterms′ d′ → participants d ⊆ participants d′
  subterms′-part⊆ᵈ {d′ = d} with d
  ... | put _ &reveal _ if _ ⇒ ds = subterms′-part⊆ᶜ {ds = ds}
  ... | withdraw _                = λ ()
  ... | split vcs                 = subterms′-part⊆ᵛ {vcs = vcs}
  ... | _ ∶ d′                    = λ x∈ → there ∘ subterms′-part⊆ᵈ {d′ = d′} x∈
  ... | after _ ∶ d′              = subterms′-part⊆ᵈ {d′ = d′}

  subterms′-part⊆ᶜ : d ∈ subterms′ ds → participants d ⊆ participants ds
  subterms′-part⊆ᶜ {ds = d ∷ ds} (here refl) = ∈-++⁺ˡ
  subterms′-part⊆ᶜ {ds = d ∷ ds} (there p)
    with ∈-++⁻ _ p
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-part⊆ᶜ {ds = ds} p′
  ... | inj₁ p′ = ∈-++⁺ˡ   ∘ subterms′-part⊆ᵈ {d′ = d} p′

  subterms′-part⊆ᵛ : d ∈ subterms′ vcs → participants d ⊆ participants vcs
  subterms′-part⊆ᵛ {vcs = (_ , []) ∷ vcs} p = ∈-++⁺ʳ _ ∘ subterms′-part⊆ᵛ {vcs = vcs} p
  subterms′-part⊆ᵛ {vcs = (_ , ds) ∷ vcs} p
    with ∈-++⁻ (subterms′ ds) p
  ... | inj₁ p′ = ∈-++⁺ˡ   ∘ subterms′-part⊆ᶜ {ds = ds} p′
  ... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms′-part⊆ᵛ {vcs = vcs} p′

subterms′-part⊆ᵃ : Valid ad → d ∈ subterms′ ad →
  participants d L.SubS.⊆ participants (ad .G)
subterms′-part⊆ᵃ {ad}{d} vad d∈ =
  Valid⇒part⊆ vad ∘ subterms′-part⊆ᶜ {ds = ad .Ad.C} d∈
