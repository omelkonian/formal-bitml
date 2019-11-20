------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------

open import Data.Nat           using (ℕ; _≟_; _>_; _+_; _∸_; _<?_)
open import Data.Product       using (Σ; Σ-syntax; proj₁; _×_; _,_)
open import Data.List          using (List; []; _∷_; [_]; length; _++_)
open import Data.String        using (String)
  renaming (length to lengthˢ)
open import Data.String.Properties using ()
  renaming (_≟_ to _≟ₛ′_)
open import Data.Bool          using (Bool; true; false; _∧_; _∨_; not)
  renaming (_≟_ to _≟ᵇ_)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True; fromWitness; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module BitML.BasicTypes
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

variable
  n : ℕ

  v v′ v″ : Value
  vs vs′ vs″ vsᶜ vsᵛ vsᵖ vsᵛₗ vsᵖₗ vsᵛᵣ vsᵖᵣ : Values

  p p′ : Participant

  s s′ s″ : Secret
  ss ss′ ssₗ ssᵣ : Secrets

++-idʳ : ∀ {A : Set} {xs : List A}
       → xs ≡ xs ++ []
++-idʳ {_} {[]}     = refl
++-idʳ {_} {x ∷ xs} = cong (x ∷_) ++-idʳ

------------------------------------------------------------------------
-- Arithmetic expressions.

data Arith :
    Secrets -- secrets referenced inside the expression
  → Set where

  `_ : ℕ → Arith []

  `len : (s : Secret) → Arith [ s ]

  _`+_ : Arith ssₗ
       → Arith ssᵣ
       → .{_ : ss ≡ ssₗ ++ ssᵣ}
       → Arith ss

  _`-_ : Arith ssₗ
       → Arith ssᵣ
       → .{_ : ss ≡ ssₗ ++ ssᵣ}
       → Arith ss

⟦_⟧ᵃ : Arith ss → ℕ
⟦ ` x    ⟧ᵃ = x
⟦ `len s ⟧ᵃ = lengthˢ s
⟦ l `+ r ⟧ᵃ = ⟦ l ⟧ᵃ + ⟦ r ⟧ᵃ
⟦ l `- r ⟧ᵃ = ⟦ l ⟧ᵃ ∸ ⟦ r ⟧ᵃ

------------------------------------------------------------------------
-- Predicates.

data Predicate :
    Secrets -- secrets referenced inside the expression
  → Set where

  `True : Predicate []

  _`∧_ : Predicate ssₗ
       → Predicate ssᵣ
       → .{_ : ss ≡ ssₗ ++ ssᵣ}
       → Predicate ss

  `¬_ : Predicate ss → Predicate ss

  _`≡_ : Arith ssₗ
       → Arith ssᵣ
       → .{_ : ss ≡ ssₗ ++ ssᵣ}
       → Predicate ss

  _`<_ : Arith ssₗ
       → Arith ssᵣ
       → .{_ : ss ≡ ssₗ ++ ssᵣ}
       → Predicate ss

⟦_⟧ᵇ : Predicate ss → Bool
⟦ `True ⟧ᵇ  = true
⟦ l `∧ r ⟧ᵇ = ⟦ l ⟧ᵇ ∧ ⟦ r ⟧ᵇ
⟦ `¬ p ⟧ᵇ   = not ⟦ p ⟧ᵇ
⟦ l `≡ r ⟧ᵇ with ⟦ l ⟧ᵃ ≟ ⟦ r ⟧ᵃ
... | yes _ = true
... | no  _ = false
⟦ l `< r ⟧ᵇ with ⟦ l ⟧ᵃ <? ⟦ r ⟧ᵃ
... | yes _ = true
... | no  _ = false

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

open import Prelude.Set' {A = Value} _≟_ using () renaming (_≟ₗ_ to _≟ₙₛ_)

-------------------------------------------------------------------
-- Contract preconditions.

-- Indices for `Precondition`.
record Preconditionⁱ : Set where
  constructor Iᵖ[_,_]
  field
    volatileDeposits   : Values
    persistentDeposits : Values
open Preconditionⁱ public
variable pi pi′ : Preconditionⁱ

data Precondition : Preconditionⁱ → Set where

  -- volatile deposit
  _:?_ : Participant → (v : Value) → Precondition Iᵖ[ [ v ] , [] ]

  -- persistent deposit
  _:!_ : Participant → (v : Value) → Precondition Iᵖ[ [] , [ v ] ]

  -- committed secret (random nonce) by <Participant>
  _:secret_ : Participant → Secret → Precondition Iᵖ[ [] , [] ]

  -- composition
  _∣_∶-_ : Precondition Iᵖ[ vsᵛₗ , vsᵖₗ ]
         → Precondition Iᵖ[ vsᵛᵣ , vsᵖᵣ ]
         → .( (vsᵛ ≡ vsᵛₗ ++ vsᵛᵣ)
            × (vsᵖ ≡ vsᵖₗ ++ vsᵖᵣ))
         → Precondition Iᵖ[ vsᵛ , vsᵖ ]

_∣_ : ∀ {vsᵛ vsᵖ vsᵛₗ vsᵖₗ vsᵛᵣ vsᵖᵣ}
    → Precondition Iᵖ[ vsᵛₗ , vsᵖₗ ]
    → Precondition Iᵖ[ vsᵛᵣ , vsᵖᵣ ]
    → {_ : True (vsᵛ ≟ₙₛ vsᵛₗ ++ vsᵛᵣ)}
    → {_ : True (vsᵖ ≟ₙₛ vsᵖₗ ++ vsᵖᵣ)}
    → Precondition Iᵖ[ vsᵛ , vsᵖ ]
(l ∣ r) {p₁} {p₂} = l ∣ r ∶- toWitness p₁ , toWitness p₂

infix  5 _:?_
infix  5 _:!_
infix  5 _:secret_
infixl 3 _∣_
infixl 2 _∣_∶-_

-------------------------------------------------------------------
-- Decidable equality, set modules.

import Prelude.Set' as SET

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

_≟ₐᵣ_ : Decidable {A = Arith ss} _≡_
(` x)  ≟ₐᵣ (` y)      with x ≟ y
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        = yes refl
(` _)    ≟ₐᵣ (_ `+ _) = no λ ()
(` _)    ≟ₐᵣ (_ `- _) = no λ ()
`len s   ≟ₐᵣ `len .s = yes refl
`len _   ≟ₐᵣ (_ `+ _) = no λ ()
`len _   ≟ₐᵣ (_ `- _) = no λ ()
(_`+_ {ssₗ = ssₗ} {ssᵣ = ssᵣ} {ss = ss}  x x′) ≟ₐᵣ (_`+_ {ssₗ = ssₗ′} {ssᵣ = ssᵣ′} {ss = ss′} y y′)
                      with ssₗ ≟ₛₛ ssₗ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with ssᵣ ≟ₛₛ ssᵣ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with x ≟ₐᵣ y
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with x′ ≟ₐᵣ y′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        = yes refl
(_ `+ _) ≟ₐᵣ (` _) = no λ ()
(_ `+ _) ≟ₐᵣ `len _ = no λ ()
(_ `+ _) ≟ₐᵣ (_ `- _) = no λ ()
(_`-_ {ssₗ = ssₗ} {ssᵣ = ssᵣ} {ss = ss}  x x′) ≟ₐᵣ (_`-_ {ssₗ = ssₗ′} {ssᵣ = ssᵣ′} {ss = ss′} y y′)
                      with ssₗ ≟ₛₛ ssₗ′
... | no ¬p           = no λ{refl → ¬p refl}
... | yes refl        with ssᵣ ≟ₛₛ ssᵣ′
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
_≟ₚᵣₑ_ : Decidable {A = Predicate ss} _≡_
`True ≟ₚᵣₑ `True       = yes refl
`True ≟ₚᵣₑ (_ `∧ _)    = no λ ()
`True ≟ₚᵣₑ (`¬ _)      = no λ ()
`True ≟ₚᵣₑ (_ `≡ _)    = no λ ()
`True ≟ₚᵣₑ (_ `< _)    = no λ ()

(_`∧_ {ssₗ = ssₗ} {ssᵣ = ssᵣ} x y) ≟ₚᵣₑ (_`∧_ {ssₗ = ssₗ′} {ssᵣ = ssᵣ′} x′ y′)
                       with ssₗ ≟ₛₛ ssₗ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with ssᵣ ≟ₛₛ ssᵣ′
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

(_`≡_ {ssₗ = ssₗ} {ssᵣ = ssᵣ} x y) ≟ₚᵣₑ (_`≡_ {ssₗ = ssₗ′} {ssᵣ = ssᵣ′} x′ y′)
                       with ssₗ ≟ₛₛ ssₗ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with ssᵣ ≟ₛₛ ssᵣ′
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

(_`<_ {ssₗ = ssₗ} {ssᵣ = ssᵣ} x y) ≟ₚᵣₑ (_`<_ {ssₗ = ssₗ′} {ssᵣ = ssᵣ′} x′ y′)
                       with ssₗ ≟ₛₛ ssₗ′
... | no ¬p            = no λ{refl → ¬p refl}
... | yes refl         with ssᵣ ≟ₛₛ ssᵣ′
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
_≟ₚᵣ_ : Decidable {A = Precondition pi} _≡_
(x :? v)      ≟ₚᵣ (x′ :? v′)      with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with v ≟ v′
... | no v≢v′                     = no λ{refl → v≢v′ refl}
... | yes refl                    = yes refl
(_ :? _)      ≟ₚᵣ (_ ∣ _ ∶- _)    = no λ ()

(x :! v)      ≟ₚᵣ (x′ :! v′)      with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with v ≟ v′
... | no v≢v′                     = no λ{refl → v≢v′ refl}
... | yes refl                    = yes refl
(_ :! _)      ≟ₚᵣ (_ ∣ _ ∶- _)         = no λ ()

(x :secret s) ≟ₚᵣ (x′ :secret s′) with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with s ≟ₛ s′
... | no s≢s′                     = no λ{refl → s≢s′ refl}
... | yes refl                    = yes refl
(_ :secret _) ≟ₚᵣ (_ ∣ _ ∶- _)         = no λ ()

(_∣_∶-_ {vsᵛₗ = vsᵛₗ} {vsᵖₗ = vsᵖₗ} {vsᵛᵣ = vsᵛᵣ} {vsᵖᵣ = vsᵖᵣ} p₁ p₂ _) ≟ₚᵣ
  (_∣_∶-_ {vsᵛₗ = vsᵛₗ′} {vsᵖₗ = vsᵖₗ′} {vsᵛᵣ = vsᵛᵣ′} {vsᵖᵣ = vsᵖᵣ′} p₁′ p₂′ _)
                                  with vsᵛₗ ≟ₙₛ vsᵛₗ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsᵛᵣ ≟ₙₛ vsᵛᵣ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsᵖₗ ≟ₙₛ vsᵖₗ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsᵖᵣ ≟ₙₛ vsᵖᵣ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with p₁ ≟ₚᵣ p₁′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with p₂ ≟ₚᵣ p₂′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    = yes refl
(_ ∣ _ ∶- _)  ≟ₚᵣ (_ :? _)        = no λ ()
(_ ∣ _ ∶- _)  ≟ₚᵣ (_ :! _)        = no λ ()
(_ ∣ _ ∶- _)  ≟ₚᵣ (_ :secret _)   = no λ ()
