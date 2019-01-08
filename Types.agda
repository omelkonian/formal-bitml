------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------

open import Data.Nat           using (ℕ; _≟_; _>_)
open import Data.Product       using (Σ; Σ-syntax; proj₁)
open import Data.List          using (List; []; _∷_; [_]; length; _++_)
open import Data.String        using (String)
open import Data.String.Unsafe using () renaming (_≟_ to _≟ₛ′_)
open import Data.Bool          using (Bool; true; false)
  renaming (_≟_ to _≟ᵇ_)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

-------------------------------------------------------------------
-- Basic types.

Hon = proj₁ Honest

Value : Set
Value = ℕ

Values : Set
Values = List Value

Secret : Set
Secret = String

Secrets : Set
Secrets = List Secret

Time : Set
Time = ℕ

------------------------------------------------------------------------
-- Arithmetic expressions.

data Arith :
    Secrets -- secrets referenced inside the expression
  → Set where

  `_ : ℕ → Arith []

  `len : (s : Secret) → Arith [ s ]

  _`+_ : ∀ {s sₗ sᵣ}
       → Arith sₗ
       → Arith sᵣ
       → .{_ : s ≡ sₗ ++ sᵣ}
       → Arith s

  _`-_ : ∀ {s sₗ sᵣ}
       → Arith sₗ
       → Arith sᵣ
       → .{_ : s ≡ sₗ ++ sᵣ}
       → Arith s

------------------------------------------------------------------------
-- Predicates.

data Predicate :
    Secrets -- secrets referenced inside the expression
  → Set where

  `True : Predicate []

  _`∧_ : ∀ {s sₗ sᵣ}
       → Predicate sₗ
       → Predicate sᵣ
       → .{_ : s ≡ sₗ ++ sᵣ}
       → Predicate s

  `¬_ : ∀ {s} → Predicate s → Predicate s

  _`≡_ : ∀ {s sₗ sᵣ}
       → Arith sₗ
       → Arith sᵣ
       → .{_ : s ≡ sₗ ++ sᵣ}
       → Predicate s

  _`<_ : ∀ {s sₗ sᵣ}
       → Arith sₗ
       → Arith sᵣ
       → .{_ : s ≡ sₗ ++ sᵣ}
       → Predicate s

-------------------------------------------------------------------
-- Deposits.

infix 30 _has_
record Deposit : Set where
  constructor _has_
  field
    participant : Participant
    value       : Value
open Deposit public

Deposits : Set
Deposits = List Deposit

record DepositRef : Set where
  constructor _⟨_⟩
  field
    deposit    : Deposit
    persistent : Bool
open DepositRef public

open import Data.Set' {A = Value} _≟_ using () renaming (_≟ₗ_ to _≟ₙₛ_)

-------------------------------------------------------------------
-- Contract preconditions.

data Precondition :
    Values -- the deposits it requires (persistent or not)
  → Set where

  -- volatile deposit of <Value>$, expected from <Participant>
  _:?_ : Participant → (v : Value) → Precondition [ v ] -- T0D0 remove v?

  -- persistent deposit of <Value>$, expected from <Participant>
  _:!_ : Participant → (v : Value) → Precondition [ v ]

  -- committed secret (random nonce) by <Participant>
  _:secret_ : Participant → Secret → Precondition []

  -- composition
  _∣_ : ∀ {vs vsₗ vsᵣ}
    → Precondition vsₗ
    → Precondition vsᵣ
    → .{_ : True (vs ≟ₙₛ vsₗ ++ vsᵣ)}
    → Precondition vs

infix  5 _:?_
infix  5 _:!_
infix  5 _:secret_
infixl 3 _∣_

-------------------------------------------------------------------
-- Decidable equality, set modules.

import Data.Set' as SET

-- Sets of values
module SETₙ = SET {A = Value} _≟_

Set⟨Value⟩ : Set
Set⟨Value⟩ = Set'
  where open SETₙ

-- Sets of participants
module SETₚ = SET {A = Participant} _≟ₚ_

Set⟨Participant⟩ : Set
Set⟨Participant⟩ = Set'
  where open SETₚ

-- Sets of deposits
_≟ₑ_ : Decidable {A = Deposit} _≡_
x ≟ₑ y with participant x ≟ₚ participant y
          | value       x ≟  value       y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl = yes refl

module SETₑ = SET {A = Deposit} _≟ₑ_

Set⟨Deposit⟩ : Set
Set⟨Deposit⟩ = Set'
  where open SETₑ

-- Sets of deposit references
_≟ₑᵣ_ : Decidable {A = DepositRef} _≡_
x ≟ₑᵣ y with deposit    x ≟ₑ deposit    y
           | persistent x ≟ᵇ persistent y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl = yes refl

module SETₑᵣ = SET {A = DepositRef} _≟ₑᵣ_

Set⟨DepositRef⟩ : Set
Set⟨DepositRef⟩ = Set'
  where open SETₑᵣ

-- Sets of secrets.
_≟ₛ_ : Decidable {A = Secret} _≡_
_≟ₛ_ = _≟ₛ′_

module SETₛ = SET {A = Secret} _≟ₛ_

Set⟨Secret⟩ : Set
Set⟨Secret⟩ = Set'
  where open SETₛ

-- Sets of arithmetic expressions.
open SETₛ  using () renaming (_≟ₗ_ to _≟ₛₛ_)

_≟ₐᵣ_ : ∀ {s} → Decidable {A = Arith s} _≡_
(` x)  ≟ₐᵣ (` y)      with x ≟ y
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        = yes refl
(` _)    ≟ₐᵣ (_ `+ _) = no λ ()
(` _)    ≟ₐᵣ (_ `- _) = no λ ()
`len s   ≟ₐᵣ `len .s = yes refl
`len _   ≟ₐᵣ (_ `+ _) = no λ ()
`len _   ≟ₐᵣ (_ `- _) = no λ ()
(_`+_ {s} {sₗ} {sᵣ} x x′) ≟ₐᵣ (_`+_ {s′} {sₗ′} {sᵣ′} y y′)
                      with sₗ ≟ₛₛ sₗ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with sᵣ ≟ₛₛ sᵣ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with x ≟ₐᵣ y
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with x′ ≟ₐᵣ y′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        = yes refl
(_ `+ _) ≟ₐᵣ (` _) = no λ ()
(_ `+ _) ≟ₐᵣ `len _ = no λ ()
(_ `+ _) ≟ₐᵣ (_ `- _) = no λ ()
(_`-_ {s} {sₗ} {sᵣ} x x′) ≟ₐᵣ (_`-_ {s′} {sₗ′} {sᵣ′} y y′)
                      with sₗ ≟ₛₛ sₗ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with sᵣ ≟ₛₛ sᵣ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with x ≟ₐᵣ y
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with x′ ≟ₐᵣ y′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        = yes refl
(_ `- _) ≟ₐᵣ (` _)    = no λ ()
(_ `- _) ≟ₐᵣ `len _   = no λ ()
(_ `- _) ≟ₐᵣ (_ `+ _) = no λ ()

-- Sets of predicates.
_≟ₚᵣₑ_ : ∀ {s} → Decidable {A = Predicate s} _≡_
`True ≟ₚᵣₑ `True       = yes refl
`True ≟ₚᵣₑ (_ `∧ _)    = no λ ()
`True ≟ₚᵣₑ (`¬ _)      = no λ ()
`True ≟ₚᵣₑ (_ `≡ _)    = no λ ()
`True ≟ₚᵣₑ (_ `< _)    = no λ ()

(_`∧_ {_} {sₗ} {sᵣ} x y) ≟ₚᵣₑ (_`∧_ {_} {sₗ′} {sᵣ′} x′ y′)
                       with sₗ ≟ₛₛ sₗ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with sᵣ ≟ₛₛ sᵣ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with x ≟ₚᵣₑ x′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with y ≟ₚᵣₑ y′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         = yes refl
(_ `∧ _) ≟ₚᵣₑ `True    = no λ ()
(_ `∧ _) ≟ₚᵣₑ (`¬ _)   = no λ ()
(_ `∧ _) ≟ₚᵣₑ (_ `≡ _) = no λ ()
(_ `∧ _) ≟ₚᵣₑ (_ `< _) = no λ ()

(`¬ x) ≟ₚᵣₑ (`¬ y)     with x ≟ₚᵣₑ y
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         = yes refl
(`¬ _) ≟ₚᵣₑ `True      = no λ ()
(`¬ _) ≟ₚᵣₑ (_ `∧ _)   = no λ ()
(`¬ _) ≟ₚᵣₑ (_ `≡ _)   = no λ ()
(`¬ _) ≟ₚᵣₑ (_ `< _)   = no λ ()

(_`≡_ {_} {sₗ} {sᵣ} x y) ≟ₚᵣₑ (_`≡_ {_} {sₗ′} {sᵣ′} x′ y′)
                       with sₗ ≟ₛₛ sₗ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with sᵣ ≟ₛₛ sᵣ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with x ≟ₐᵣ x′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with y ≟ₐᵣ y′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         = yes refl
(_ `≡ _) ≟ₚᵣₑ `True    = no λ ()
(_ `≡ _) ≟ₚᵣₑ (`¬ _)   = no λ ()
(_ `≡ _) ≟ₚᵣₑ (_ `∧ _) = no λ ()
(_ `≡ _) ≟ₚᵣₑ (_ `< _) = no λ ()

(_`<_ {_} {sₗ} {sᵣ} x y) ≟ₚᵣₑ (_`<_ {_} {sₗ′} {sᵣ′} x′ y′)
                       with sₗ ≟ₛₛ sₗ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with sᵣ ≟ₛₛ sᵣ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with x ≟ₐᵣ x′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with y ≟ₐᵣ y′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         = yes refl
(_ `< _) ≟ₚᵣₑ `True    = no λ ()
(_ `< _) ≟ₚᵣₑ (`¬ _)   = no λ ()
(_ `< _) ≟ₚᵣₑ (_ `∧ _) = no λ ()
(_ `< _) ≟ₚᵣₑ (_ `≡ _) = no λ ()

-- Sets of preconditions.
_≟ₚᵣ_ : ∀ {vs} → Decidable {A = Precondition vs} _≡_
(x :? v)      ≟ₚᵣ (x′ :? v′)      with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with v ≟ v′
... | no v≢v′                     = no λ{refl → v≢v′ refl}
... | yes refl                    = yes refl
(_ :? _)      ≟ₚᵣ (_ :! _)        = no λ ()
(_ :? _)      ≟ₚᵣ (_ ∣ _)         = no λ ()

(x :! v)      ≟ₚᵣ (x′ :! v′)      with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with v ≟ v′
... | no v≢v′                     = no λ{refl → v≢v′ refl}
... | yes refl                    = yes refl
(_ :! _)      ≟ₚᵣ (_ :? _)        = no λ ()
(_ :! _)      ≟ₚᵣ (_ ∣ _)         = no λ ()

(x :secret s) ≟ₚᵣ (x′ :secret s′) with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with s ≟ₛ s′
... | no s≢s′                     = no λ{refl → s≢s′ refl}
... | yes refl                    = yes refl
(_ :secret _) ≟ₚᵣ (_ ∣ _)         = no λ ()

(_∣_ {_} {vsˡ}  {vsʳ}  p₁  p₂) ≟ₚᵣ (_∣_ {_} {vsˡ′} {vsʳ′} p₁′ p₂′)
                                  with vsˡ ≟ₙₛ vsˡ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsʳ ≟ₙₛ vsʳ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with p₁ ≟ₚᵣ p₁′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with p₂ ≟ₚᵣ p₂′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    = yes refl
(_ ∣ _)       ≟ₚᵣ (_ :? _)        = no λ ()
(_ ∣ _)       ≟ₚᵣ (_ :! _)        = no λ ()
(_ ∣ _)       ≟ₚᵣ (_ :secret _)   = no λ ()
