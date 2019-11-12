------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------

open import Level    using (Level)
open import Function using (_∘_)

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Nat     using (_>_)
open import Data.List    using (List; []; _∷_; length; _++_)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any                   using (Any; here; there; index)
open import Data.List.Relation.Unary.All                   using (All; all)
open import Data.List.Relation.Unary.Unique.Propositional  using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Product   using (_×-dec_)
open import Relation.Binary            using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate.Base

module BitML.Contracts.Validity
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types   Participant _≟ₚ_ Honest hiding (B)
open import BitML.Contracts.Helpers Participant _≟ₚ_ Honest

ValidAdvertisement : Advertisement → Set
ValidAdvertisement (⟨ G ⟩ C) =
    -- (i) names in G are distinct
    Unique (namesᵖ G)

    -- (ii) each name in C appears in G
  × namesᶜˢ C ⊆ namesᵖ G

    -- (iii) the names in put_&reveal_ are distinct and secrets in `if ...` appear in `reveal ...`
  × All (λ{ (xs , as , p) → Unique xs × (secretsᵖʳ p ⊆ as)}) (putComponentsᶜˢ C)

    -- (iv) each participant has a persistent deposit in G
  × participantsᵖ G ++ participantsᶜˢ C ⊆ persistentParticipantsᵖ G

-- Decision procedure.
validAd? : ∀ (ad : Advertisement) → Dec (ValidAdvertisement ad)
validAd? (⟨ G ⟩ C) =
        SETₙ.unique? (namesᵖ G)
  ×-dec namesᶜˢ C SETₙ.⊆? namesᵖ G
  ×-dec all (λ{ (xs , as , p) → SETₛ.unique? xs ×-dec (secretsᵖʳ p SETₛ.⊆? as)}) (putComponentsᶜˢ C)
  ×-dec participantsᵖ G ++ participantsᶜˢ C SETₚ.⊆? persistentParticipantsᵖ G

-- Mapping while preserving validity.
private
  variable
    ℓ : Level
    B : Set ℓ

record _~_ (d : Contract) (ds : Contracts) : Set where
  constructor _&_
  field
    put⊆   : putComponentsᶜ d ⊆ putComponentsᶜˢ ds
    names⊆ : namesᶜ         d ⊆ namesᶜˢ         ds

map~ : (ds : Contracts) → (∀ (d : Contract) → d ~ ds → B) → List B
map~ ds f = mapWith∈ ds λ {d} d∈ → f d (∈⇒~ d∈)
  where
    ∈⇒~ : ∀ {d ds} → d ∈ ds → d ~ ds
    ∈⇒~ (here refl) = ∈-++⁺ˡ & ∈-++⁺ˡ
    ∈⇒~ (there d∈)  with ∈⇒~ d∈
    ... | p⊆ & s⊆   = (∈-++⁺ʳ _ ∘ p⊆) & (∈-++⁺ʳ _ ∘ s⊆)

record _~′_ (ds : Contracts) (ds′ : Contracts) : Set where
  constructor _&_
  field
    put⊆   : putComponentsᶜˢ ds ⊆ putComponentsᶜˢ ds′
    names⊆ : namesᶜˢ         ds ⊆ namesᶜˢ         ds′

map~′ : (ds : Contracts) → ds ~′ ds′ → (∀ (d : Contract) → d ~ ds′ → B) → List B
map~′ ds (p⊆′ & n⊆′) f = map~ ds λ{ d (p⊆ & n⊆) → f d ((p⊆′ ∘ p⊆) & (n⊆′ ∘ n⊆)) }

record _~″_ (vcs : List (Value × Contracts)) (ds′ : Contracts) : Set where
  constructor _&_
  field
    put⊆   : putComponentsᵛᶜˢ vcs ⊆ putComponentsᶜˢ ds′
    names⊆ : namesᵛᶜˢ         vcs ⊆ namesᶜˢ         ds′

mapEnum~″ : (vcs : List (Value × Contracts))
          → vcs ~″ ds′
          → (∀ (i : Index vcs) (v : Value) (ds : Contracts) → ds ~′ ds′ → B)
          → List B
mapEnum~″ vcs (p⊆ & n⊆) f = mapWith∈ vcs λ{ {(v , ds)} x∈ → f (index x∈) v ds ((p⊆ ∘ ∈⇒p⊆ x∈) & (n⊆ ∘ ∈⇒n⊆ x∈)) }
  where
    ∈⇒p⊆ : ∀ {v ds vcs} → (v , ds) ∈ vcs → putComponentsᶜˢ ds ⊆ putComponentsᵛᶜˢ vcs
    ∈⇒p⊆ (here refl) = ∈-++⁺ˡ
    ∈⇒p⊆ (there x∈)  = ∈-++⁺ʳ _ ∘ ∈⇒p⊆ x∈

    ∈⇒n⊆ : ∀ {v ds vcs} → (v , ds) ∈ vcs → namesᶜˢ ds ⊆ namesᵛᶜˢ vcs
    ∈⇒n⊆ (here refl) = ∈-++⁺ˡ
    ∈⇒n⊆ (there x∈)  = ∈-++⁺ʳ _ ∘ ∈⇒n⊆ x∈

map~″ : (vcs : List (Value × Contracts))
      → vcs ~″ ds′
      → (∀ (v : Value) (ds : Contracts) → ds ~′ ds′ → B)
      → List B
map~″ vcs vcs~ f = mapEnum~″ vcs vcs~ λ _ → f
