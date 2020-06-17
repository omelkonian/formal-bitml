------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --postfix-projections #-}

open import Level    using (Level; 0ℓ)
open import Function using (_∘_; _$_; id; const)

open import Data.Product using (_×_; _,_; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Nat     using (ℕ; suc; _+_; _<_; _>_)
open import Data.Nat.Properties using (<-trans)

open import Data.List using (List; []; _∷_; [_]; length; _++_; map; concat; concatMap; sum)
open import Data.List.NonEmpty using (List⁺)
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any                   using (Any; here; there; index)
open import Data.List.Relation.Unary.All                   using (All; all)
open import Data.List.Relation.Unary.Unique.Propositional  using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Product   using (_×-dec_)
open import Relation.Binary            using (Decidable; Transitive; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'
open import Prelude.Measurable

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
open import BitML.Contracts.Induction Participant Honest

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
  ×-dec all (λ{ (xs , as , p) → unique? xs ×-dec (secrets p ⊆? as)}) (putComponents C)
  ×-dec participants G ++ participants C ⊆? persistentParticipants G

----------


-- Mapping while preserving validity.

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

len : ∀ {{_ : C₁ has Contract}} → C₁ → ℕ
len x = ∣ contracts x ∣

len>0 : ∀ {{_ : C₁ has Contract}} (x : C₁)
  → len x > 0
len>0 x with contracts x
... | []    = Data.Nat.s≤s Data.Nat.z≤n
... | _ ∷ _ = {!!}

postulate
  +-helper : ∀ {x y z} → x ≡ y + z → y > 0 → z > 0 → (y < x) × (z < x)

CC : Set _
CC = Σ[ A ∈ Set ] (CC-like A) × A

toCC : ∀ {{_ : CC-like C₁}} → C₁ → CC
toCC {C₁} {{CC-C₁}} x = C₁ , CC-C₁ , x

instance
  Measurable-CC : Measurable CC
  Measurable-CC .∣_∣ (_ , record {hc = hc} , x) = len {{hc}} x

-- ∣_∣ : ∀ {{_ : CC-like C₁}} → C₁ → ℕ
-- ∣_∣ = sum ∘ map ∣_∣ᶜ ∘ contracts

len-∷ : ∀ {{_ : CC-like C₁}} (x : C₁) (xs : List C₁)
  → len (x ∷ xs) ≡ len x + len xs
len-∷ = {!!}

∈⇒≺ : ∀ {{_ : CC-like C₁}} {x : C₁} {xs : List C₁} → x ∈ xs → toCC x ≺ toCC xs
∈⇒≺ {x}{xs} (here  {_}{xs′} refl) = proj₁ $ +-helper (len-∷ xs xs′) (len>0 xs) (len>0 xs′)
∈⇒≺ {x}{xs} (there {x′}{xs′} x∈)  = <-trans (∈⇒≺ x∈) (proj₂ $ +-helper (len-∷ x′ xs′) (len>0 x′) (len>0 xs′))

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

map∈-⊆≺ : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {z : C₂}
  → (xs : List C₁)
  → xs ⊆ᶜ z
  → (∀ {x : C₁} → x ∈ xs → x ⊆ᶜ z → toCC x ≺ toCC xs → B)
  → List B
map∈-⊆≺ xs xs⊆z f = mapWith∈ xs λ {x} x∈ → f x∈ (⊆ᶜ-trans (∈⇒⊆ᶜ x∈) xs⊆z) (∈⇒≺ x∈)

map-⊆≺ : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {z : C₂}
  → (xs : List C₁)
  → xs ⊆ᶜ z
  → (∀ (x : C₁) → x ⊆ᶜ z → toCC x ≺ toCC xs → B)
  → List B
map-⊆≺ xs xs⊆ᶜz f = map∈-⊆≺ xs xs⊆ᶜz (λ {x} _ → f x)

map-⊆ : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {z : C₂}
  → (xs : List C₁)
  → xs ⊆ᶜ z
  → (∀ (x : C₁) → x ⊆ᶜ z → B)
  → List B
map-⊆ xs xs⊆ᶜz f = map-⊆≺ xs xs⊆ᶜz (λ x x⊆ _ → f x x⊆)

map-≺ : ∀ {{_ : CC-like C₁}} {{_ : CC-like C₂}} {z : C₂}
  → (xs : List C₁)
  → (∀ (x : C₁) → toCC x ≺ toCC xs → B)
  → List B
map-≺ xs f = map-⊆≺ xs (⊆ᶜ-refl xs) (λ x _ x≺ → f x x≺)
