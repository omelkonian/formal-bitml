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

module BitML.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
open import Types Participant _≟ₚ_ Honest

------------------------------------------------------------------------
-- Contracts

data Contract : Value  -- the monetary value it carries
              → Values -- the volatile deposits it presumes (kind of a DeBruijn encoding)
              → Set

-- Lists of contracts.
Contracts : Value → Values → Set
Contracts v vs = List (Contract v vs)

∃Contracts : Set
∃Contracts = ∃[ v ] ∃[ vs ] Contracts v vs

ContractCases : Values → Set
ContractCases vs = List (∃[ v ] Contract v vs)

infixr 9 _∶_

infixr 5 _⊕_
infix  8 _∙

_⊕_ : ∀ {A : Set} → A → List A → List A
_⊕_ = _∷_

_∙ : ∀ {A : Set} → A → List A
_∙ = [_]

infix 1 _⊸_
_⊸_ : ∀ {vs : Values}
    → (v : Value)
    → Contract v vs
    → ∃[ v ] Contract v vs
_⊸_ {vs} v c = v , c

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

sound-put : ∀ {vs vs′ vs″} → {p : put? vs vs′ vs″} → Put vs vs′ vs″
sound-put {vs} {vs′} {vs″} {p} with vs SB.⊆? vs″
... | no _       = ⊥-elim p
... | yes vs⊆vs″ with vs′ SETₙ.≟ₗ complement-⊆ vs⊆vs″
... | no _       = ⊥-elim p
... | yes refl   = vs⊆vs″ , refl

data Contract where

  -- collect deposits and secrets
  put_&reveal_if_⇒_∶-_ : ∀ {v v′ vs′ s′ vs″}
                       → (vs : Values)
                       → (s : Secrets)
                       → Predicate s′
                       → Contracts v′ vs′
                       → .( Put vs vs′ vs″
                          × (v′ ≡ v + sum vs)
                          × (s′ SETₛ.⊆ s)
                          )
                       → Contract v vs″

  -- transfer the balance to a participant
  withdraw : ∀ {v vs} → Participant → Contract v vs

  -- split the balance
  split_∶-_ : ∀ {v vs} (cs : ContractCases vs)
            → .(v ≡ sum (map proj₁ cs))
            → Contract v vs

  -- wait for participant's authorization
  _∶_ : ∀ {v vs} → Participant → Contract v vs → Contract v vs

  -- wait of a period of time
  after_∶_ : ∀ {v vs} → Time → Contract v vs → Contract v vs

-- Implicit-proof-style operators.
split_ : ∀ {v vs} (cs : ContractCases vs) → {p : True (v ≟ sum (map proj₁ cs))} → Contract v vs
(split cs) {p} = split cs ∶- toWitness p

put_&reveal_if_⇒_ : ∀ {v v′ vs′ s′ vs″}
  → (vs : Values)
  → (s : Secrets)
  → Predicate s′
  → Contracts v′ vs′
  → .{p₁ : put? vs vs′ vs″}
  → .{p₂ : True (v′ ≟ v + sum vs)}
  → .{p₃ : s′ SETₛ.⊆? s}
  → Contract v vs″
(put vs &reveal s if p ⇒ c) {p₁} {p₂} {p₃} =
  put vs &reveal s if p ⇒ c
  ∶- (sound-put {p = p₁} , toWitness p₂ , SETₛ.sound-⊆ {p = p₃})

------------------------------------------------------------------------
-- Utilities.

secretsᵖ : ∀ {vsᵛ vsᵖ} → Participant → Precondition vsᵛ vsᵖ → Secrets
secretsᵖ _ (_ :? _)      = []
secretsᵖ _ (_ :! _)      = []
secretsᵖ A (B :secret s) with A SETₚ.≣ B
... | yes _ = [ s ]
... | no  _ = []
secretsᵖ A (l ∣ r ∶- _)  = secretsᵖ A l ++ secretsᵖ A r

participantsᶜ : ∀ {v vs} → Contracts v vs → List Participant
participantsᶜ = concatMap go
  where
    goᶜ : ∀ {vs} → ContractCases vs → List Participant
    goˢ : ∀ {v vs} → Contracts v vs → List Participant
    go  : ∀ {v vs} → Contract v vs → List Participant

    goᶜ []             = []
    goᶜ ((_ , c) ∷ cs) = go c ++ goᶜ cs

    goˢ []       = []
    goˢ (c ∷ cs) = go c ++ goˢ cs

    go (put _ &reveal _ if _ ⇒ c ∶- _) = goˢ c
    go (withdraw p)                    = [ p ]
    go (split cs ∶- _)                 = goᶜ cs
    go (p ∶ c)                         = p ∷ go c
    go (after _ ∶ c)                   = go c

participantsᵍ : ∀ {vsᵛ vsᵖ} → Precondition vsᵛ vsᵖ → List Participant
participantsᵍ (p :? _)       = [ p ]
participantsᵍ (p :! _)       = [ p ]
participantsᵍ (p :secret _)  = [ p ]
participantsᵍ (p₁ ∣ p₂ ∶- _) = participantsᵍ p₁ ++ participantsᵍ p₂

depositsᵖ : ∀ {vsᵛ vsᵖ} → Precondition vsᵛ vsᵖ → List DepositRef
depositsᵖ (p₁ ∣ p₂ ∶- _) = depositsᵖ p₁ ++ depositsᵖ p₂
depositsᵖ (a :! v)       = [ (a has v ⟨ true  ⟩) ]
depositsᵖ (a :? v)       = [ (a has v ⟨ false ⟩) ]
depositsᵖ (_ :secret _)  = []

persistentDepositsᵖ : ∀ {vsᵛ vsᵖ} → Precondition vsᵛ vsᵖ → List Deposit
persistentDepositsᵖ = map deposit ∘ filter ((_≟ᵇ true) ∘ persistent) ∘ depositsᵖ

toStipulate : ∀ {vsᵛ vsᵖ} → Precondition vsᵛ vsᵖ → List (Participant × Value)
toStipulate (p :! v)     = [ p , v ]
toStipulate (l ∣ r ∶- _) = toStipulate l ++ toStipulate r
toStipulate _            = []

------------------------------------------------------------------------
-- Advertisements.

module _ where

  infix 2 ⟨_⟩_∶-_
  record Advertisement (v : Value) (vsᶜ vsᵛ vsᵖ : Values) : Set where
    constructor ⟨_⟩_∶-_

    field
      G : Precondition vsᵛ vsᵖ
      C : Contracts v vsᶜ

      .valid : -- 1. each name in C appears in G
               vsᶜ ≾ vsᵛ

               -- 2. each participant has a persistent deposit in G
             × participantsᵍ G ++ participantsᶜ C
                 SETₚ.⊆
               (participant <$> persistentDepositsᵖ G)

               -- 3. the contract's monetary value is the sum of all the persistent deposits in G
             × v ≡ sum vsᵖ

               -- *** correct by construction ***
               -- - names in G are distinct
               -- - secrets in `if ...` appear in `reveal ...`
               -- - the names in put_&_ are distinct

  open Advertisement public

∃Advertisement : Set
∃Advertisement = ∃[ v ] ∃[ vsᶜ ] ∃[ vsᵛ ] ∃[ vsᵖ ] Advertisement v vsᶜ vsᵛ vsᵖ

infix 2 put_&reveal_if_⇒_∶-_
infixr 9 _&_

_&_ : ∀ {A B : Set} → A → B → A × B
_&_ = _,_

depositsᵃ : ∀ {v vsᶜ vsᵛ vsᵖ} → Advertisement v vsᶜ vsᵛ vsᵖ → List DepositRef
depositsᵃ ad = depositsᵖ (G ad)
