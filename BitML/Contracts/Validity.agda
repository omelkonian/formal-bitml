------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------
open import Function using (id)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Measurable
open import Prelude.Collections

open import BitML.BasicTypes
open import BitML.Predicate hiding (∣_∣)

-- open import Induction.WellFounded

module BitML.Contracts.Validity
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest hiding (B)
open import BitML.Contracts.Helpers Participant Honest

ValidAdvertisement : Advertisement → Set
ValidAdvertisement (⟨ G ⟩ C) =
    -- (i) names in G are distinct
    Unique (names G)

    -- (ii) each name in C appears in G
  × names C ⊆ names G

    -- (iii) the names in put_&reveal_ are distinct and secrets in `if ...` appear in `reveal ...`
  × All (λ{ (xs , as , p) → Unique xs × (secrets p ⊆ as)}) (putComponents C)

    -- (iv) each participant has a persistent deposit in G
  × participants G ++ participants C ⊆ persistentParticipants G

-- Decision procedure.
validAd? : ∀ (ad : Advertisement) → Dec (ValidAdvertisement ad)
validAd? (⟨ G ⟩ C) =
        unique? (names G)
  ×-dec names C ⊆? names G
  ×-dec all? (λ{ (xs , as , p) → unique? xs ×-dec (secrets p ⊆? as)}) (putComponents C)
  ×-dec participants G ++ participants C ⊆? persistentParticipants G

{-
------------------------------------------
-- *** Mapping while preserving validity.

private
  variable
    B : Set
    C₁ C₂ C₃ : Set

record CC-like (A : Set) : Set where
  field
    {{hc}} : A has Contract
    {{hp}} : A has PutComponent
    {{hn}} : A has Name
open CC-like {{...}} public

instance
  HCᶜ : Contract has Contract
  HCᶜ = record {collect = [_]}

  CCᶜ : CC-like Contract
  CCᶜ = record {hc = record {collect = collect}; hp = record {collect = collect}; hn = record {collect = collect}}

  CC-× : ∀ {V A : Set} {{_ : CC-like A}} → CC-like (V × A)
  CC-× = record { hc = record {collect = collect ∘ proj₂}
                ; hp = record {collect = collect ∘ proj₂}
                ; hn = record {collect = collect ∘ proj₂}
                }

  CC-List : ∀ {A : Set} {{_ : CC-like A}} → CC-like (List A)
  CC-List {{record {hc = hc; hp = hp; hn = hn}}}
        = record { hc = record {collect = collect {{H-List {{hc}}}}}
                 ; hp = record {collect = collect {{H-List {{hp}}}}}
                 ; hn = record {collect = collect {{H-List {{hn}}}}}
                 }

--

record _⊆ᶜ_ {{_ : CC-like C₁}} {{_ : CC-like C₂}} (x : C₁) (y : C₂) : Set where
  constructor _&_
  field
    put⊆ : putComponents x ⊆ putComponents y
    names⊆ : names x ⊆ names y

⊆ᶜ-refl : ∀ {{_ : CC-like C₁}} (c : C₁) → c ⊆ᶜ c
⊆ᶜ-refl _ = id & id

⊆ᶜ-trans : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {{_ : CC-like C₃}}
            {c₁ : C₁} {c₂ : C₂} {c₃ : C₃}
  → c₁ ⊆ᶜ c₂ → c₂ ⊆ᶜ c₃ → c₁ ⊆ᶜ c₃
⊆ᶜ-trans c₁⊆ᶜc₂ c₂⊆ᶜc₃ =
  let p⊆  & s⊆  = c₁⊆ᶜc₂
      p⊆′ & s⊆′ = c₂⊆ᶜc₃
  in  (p⊆′ ∘ p⊆) & (s⊆′ ∘ s⊆)

contracts-∷ : ∀ {{_ : CC-like C₁}} {x : C₁} {xs : List C₁}
  → contracts (x ∷ xs) ≡ contracts x ++ contracts xs

contracts-∷ {x = x}{xs} rewrite concatMap-∷ {x = x}{xs}{contracts} = refl
putComponents-∷ : ∀ {{_ : CC-like C₁}} {x : C₁} {xs : List C₁}
    → putComponents (x ∷ xs) ≡ putComponents x ++ putComponents xs
putComponents-∷ {x = x}{xs} rewrite contracts-∷ {x = x}{xs}
                                  | concatMap-++ {xs = contracts x}{contracts xs}{putComponents}
                                  = refl

names-∷ : ∀ {{_ : CC-like C₁}} {x : C₁} {xs : List C₁}
    → names (x ∷ xs) ≡ names x ++ names xs
names-∷ {x = x}{xs} rewrite contracts-∷ {x = x}{xs}
                          | concatMap-++ {xs = contracts x}{contracts xs}{names}
                          = refl

∈⇒⊆ᶜ : ∀ {{_ : CC-like C₁}} {x : C₁} {xs : List C₁} → x ∈ xs → x ⊆ᶜ xs
∈⇒⊆ᶜ {x = x}{xs} (here {xs = xs′} refl) = ⊆ᶜ-∷ˡ {x = x}{xs′}
  where
    ⊆ᶜ-∷ˡ : ∀ {{_ : CC-like C₁}} {x : C₁} {xs : List C₁}
      → x ⊆ᶜ (x ∷ xs)
    ⊆ᶜ-∷ˡ {x = x}{xs} = l & r
      where
        l : putComponents x ⊆ putComponents (x ∷ xs)
        l rewrite putComponents-∷ {x = x}{xs} = ∈-++⁺ˡ

        r : names x ⊆ names (x ∷ xs)
        r rewrite names-∷ {x = x}{xs} = ∈-++⁺ˡ
∈⇒⊆ᶜ {x = x}{xs} (there {xs = xs′} x∈)  = ⊆ᶜ-∷ʳ {x = x} {xs = xs′} (∈⇒⊆ᶜ x∈)
  where
    ⊆ᶜ-∷ʳ : ∀ {{_ : CC-like C₁}} {x x′ : C₁} {xs : List C₁}
      → x ⊆ᶜ xs
      → x ⊆ᶜ (x′ ∷ xs)
    ⊆ᶜ-∷ʳ {x = x}{x′}{xs} (p⊆ & n⊆) = (l ∘ p⊆) & (r ∘ n⊆)
      where
        l : putComponents xs ⊆ putComponents (x′ ∷ xs)
        l rewrite putComponents-∷ {x = x′}{xs} = ∈-++⁺ʳ _

        r : names xs ⊆ names (x′ ∷ xs)
        r rewrite names-∷ {x = x′}{xs} = ∈-++⁺ʳ _

map∈-⊆ : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {z : C₂}
  → (xs : List C₁)
  → xs ⊆ᶜ z
  → (∀ {x : C₁} → x ∈ xs → x ⊆ᶜ z → B)
  → List B
map∈-⊆ xs xs⊆z f = mapWith∈ xs λ {x} x∈ → f x∈ (⊆ᶜ-trans (∈⇒⊆ᶜ x∈) xs⊆z)

map-⊆ : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {z : C₂}
  → (xs : List C₁)
  → xs ⊆ᶜ z
  → (∀ (x : C₁) → x ⊆ᶜ z → B)
  → List B
map-⊆ xs xs⊆ᶜz f = map∈-⊆ xs xs⊆ᶜz (λ {x} _ → f x)
-}
