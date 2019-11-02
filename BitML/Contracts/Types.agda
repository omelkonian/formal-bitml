------------------------------------------------------------------------
-- BitML datatypes: Contracts & Advertisements
------------------------------------------------------------------------

open import Level    using (0ℓ)
open import Function using (_on_; const; _∘_; id; _∋_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (tt; ⊤)
open import Data.Bool    using (T; true; false)
  renaming (_≟_ to _≟ᵇ_)
open import Data.List    using ( List; []; _∷_; [_]; _++_
                               ; map; concat; concatMap; length; sum; foldr; filter
                               )
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; ∃-syntax; Σ; Σ-syntax)

open import Data.List.Any using (Any; any; here; there)
open import Data.List.Any.Properties using (any⁺)
import Data.List.Relation.Pointwise as PW

open import Data.Nat using ( ℕ; zero; suc; _<_; _>_; _+_; _∸_
                           ; _≤_; z≤n; s≤s; _≤?_; _≥?_; _≟_
                           )
open import Data.Nat.Properties using (<-trans; <-cmp; +-identityʳ; m∸n+n≡m)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; True)
open import Relation.Binary  using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

open import Prelude.Lists

module BitML.Contracts.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.BasicTypes Participant _≟ₚ_ Honest

------------------------------------------------------------------------
-- Contracts

-- Indices for `Contract`.
record Contractⁱ : Set where
  constructor Iᶜ[_,_]
  field
    contractValue    : Value   -- the monetary value it carries
    volatileDeposits : Values  -- the volatile deposits it presumes (kind of a DeBruijn encoding)
open Contractⁱ public

data Contract : Contractⁱ → Set

∃Contract : Set
∃Contract = ∃[ ci ] Contract ci


-- Lists of contracts.
Contracts : Contractⁱ → Set
Contracts ci = List (Contract ci)

∃Contracts : Set
∃Contracts = ∃[ ci ] Contracts ci

ContractCases : Values → Set
ContractCases vs = List (∃[ v ] Contract Iᶜ[ v , vs ])

variable
  ci ci′ : Contractⁱ
  c : Contract ci
  c′ : Contract ci′

infixr 9 _∶_

infixr 5 _⊕_
infix  8 _∙

_⊕_ : ∀ {A : Set} → A → List A → List A
_⊕_ = _∷_

_∙ : ∀ {A : Set} → A → List A
_∙ = [_]

infix 1 _⊸_
_⊸_ : (v : Value)
    → Contract Iᶜ[ v , vs ]
    → ∃[ v ] Contract Iᶜ[ v , vs ]
_⊸_ v c = v , c

open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)

Put : Values → Values → Values → Set
Put vs vs′ vs″ = Σ[ p ∈ vs ⊆ vs″ ] (vs′ ≡ complement-⊆ p)

import Data.List.Relation.Binary.Sublist.DecPropositional {A = Value} _≟_ as SB

put? : Values → Values → Values → Set
put? vs vs′ vs″ with vs SB.⊆? vs″
... | no _      = ⊥
... | yes p     with vs′ SETₙ.≟ₗ complement-⊆ p
... | no _      = ⊥
... | yes refl  = ⊤

sound-put : ∀ {p : put? vs vs′ vs″} → Put vs vs′ vs″
sound-put {vs = vs} {vs′ = vs′} {vs″ = vs″} {p = p}
  with vs SB.⊆? vs″
... | no _       = ⊥-elim p
... | yes vs⊆vs″ with vs′ SETₙ.≟ₗ complement-⊆ vs⊆vs″
... | no _       = ⊥-elim p
... | yes refl   = vs⊆vs″ , refl

data Contract where

  -- collect deposits and secrets
  put_&reveal_if_⇒_∶-_ : (vs : Values)
                       → (ss : Secrets)
                       → Predicate ss′
                       → Contracts Iᶜ[ v′ , vs′ ]
                       → .( Put vs vs′ vs″
                          × (v′ ≡ v + sum vs)
                          × (ss′ SETₛ.⊆ ss)
                          )
                       → Contract Iᶜ[ v , vs″ ]

  -- transfer the balance to a participant
  withdraw : Participant → Contract ci

  -- split the balance
  split_∶-_ : (cs : ContractCases vs)
            → .(v ≡ sum (map proj₁ cs))
            → Contract Iᶜ[ v , vs ]

  -- wait for participant's authorization
  _∶_ : Participant → Contract ci → Contract ci

  -- wait of a period of time
  after_∶_ : Time → Contract ci → Contract ci

-- Implicit-proof-style operators.
split_ : (cs : ContractCases vs) → {p : True (v ≟ sum (map proj₁ cs))} → Contract Iᶜ[ v , vs ]
(split cs) {p} = split cs ∶- toWitness p

put_&reveal_if_⇒_ :
    (vs : Values)
  → (ss : Secrets)
  → Predicate ss′
  → Contracts Iᶜ[ v′ , vs′ ]
  → .{p₁ : put? vs vs′ vs″}
  → .{p₂ : True (v′ ≟ v + sum vs)}
  → .{p₃ : ss′ SETₛ.⊆? ss}
  → Contract Iᶜ[ v , vs″ ]
(put vs &reveal s if p ⇒ c) {p₁} {p₂} {p₃} =
  put vs &reveal s if p ⇒ c
  ∶- (sound-put {p = p₁} , toWitness p₂ , SETₛ.sound-⊆ {p = p₃})

------------------------------------------------------------------------
-- Utilities.

secretsᵖ : Participant → Precondition pi → Secrets
secretsᵖ _ (_ :? _)      = []
secretsᵖ _ (_ :! _)      = []
secretsᵖ A (B :secret s) with A SETₚ.≣ B
... | yes _ = [ s ]
... | no  _ = []
secretsᵖ A (l ∣ r ∶- _)  = secretsᵖ A l ++ secretsᵖ A r

participantsᶜ : Contracts ci → List Participant
participantsᶜ = concatMap go
  where
    goᶜ : ContractCases vs → List Participant
    goˢ : Contracts ci → List Participant
    go  : Contract ci → List Participant

    goᶜ []             = []
    goᶜ ((_ , c) ∷ cs) = go c ++ goᶜ cs

    goˢ []       = []
    goˢ (c ∷ cs) = go c ++ goˢ cs

    go (put _ &reveal _ if _ ⇒ c ∶- _) = goˢ c
    go (withdraw p)                    = [ p ]
    go (split cs ∶- _)                 = goᶜ cs
    go (p ∶ c)                         = p ∷ go c
    go (after _ ∶ c)                   = go c

participantsᵍ : Precondition pi → List Participant
participantsᵍ (p :? _)       = [ p ]
participantsᵍ (p :! _)       = [ p ]
participantsᵍ (p :secret _)  = [ p ]
participantsᵍ (p₁ ∣ p₂ ∶- _) = participantsᵍ p₁ ++ participantsᵍ p₂

depositsᵖ : Precondition pi → List DepositRef
depositsᵖ (p₁ ∣ p₂ ∶- _) = depositsᵖ p₁ ++ depositsᵖ p₂
depositsᵖ (a :! v)       = [ (a has v ⟨ true  ⟩) ]
depositsᵖ (a :? v)       = [ (a has v ⟨ false ⟩) ]
depositsᵖ (_ :secret _)  = []

persistentDepositsᵖ : Precondition pi → List Deposit
persistentDepositsᵖ = map deposit ∘ filter ((_≟ᵇ true) ∘ persistent) ∘ depositsᵖ

toStipulate : Precondition pi → List (Participant × Value)
toStipulate (p :! v)     = [ p , v ]
toStipulate (l ∣ r ∶- _) = toStipulate l ++ toStipulate r
toStipulate _            = []

------------------------------------------------------------------------
-- Advertisements.

infix 2 ⟨_⟩_∶-_
record Advertisement (ci : Contractⁱ) (pi : Preconditionⁱ) : Set where
  constructor ⟨_⟩_∶-_

  field
    G : Precondition pi
    C : Contracts ci

    .valid : -- 1. each name in C appears in G
             volatileDeposits ci ≾ volatileDeposits pi

             -- 2. each participant has a persistent deposit in G
           × participantsᵍ G ++ participantsᶜ C
               SETₚ.⊆
             (participant <$> persistentDepositsᵖ G)

           -- 3. the contract's monetary value is the sum of all the persistent deposits in G
           × contractValue ci ≡ sum (persistentDeposits pi)

           -- *** correct by construction ***
           -- - names in G are distinct
           -- - secrets in `if ...` appear in `reveal ...`
           -- - the names in put_&_ are distinct

open Advertisement public
variable ad : Advertisement ci pi

∃Advertisement : Set
∃Advertisement = ∃[ ci ] ∃[ pi ] Advertisement ci pi

infix 2 put_&reveal_if_⇒_∶-_
infixr 9 _&_

_&_ : ∀ {A B : Set} → A → B → A × B
_&_ = _,_

depositsᵃ : Advertisement ci pi → List DepositRef
depositsᵃ ad = depositsᵖ (G ad)
