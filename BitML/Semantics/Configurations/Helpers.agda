------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Function     using (_∘_)
open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe   using (Maybe; just; nothing; maybe′)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Data.List using (List; []; _∷_; [_]; _++_; map; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; False; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Helpers
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest

-------------------------------------------------------------------

-- Re-ordering configurations
cfgToList : Configuration → List Configuration
cfgToList ∅ᶜ       = []
cfgToList (l ∣ r) = cfgToList l ++ cfgToList r
cfgToList c        = [ c ]

infix 3 _≈_
_≈_ : Configuration → Configuration → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′

infix 3 _≈?_
_≈?_ : Decidable {A = Configuration} _≈_
-- _≈?_ : Configuration → Configuration → Set
c ≈? c′ = cfgToList c ↭? cfgToList c′

instance
  HDᶜᶠ : Configuration has DepositRef
  HDᶜᶠ .collect cf with cf
  ... | ⟨ A has v ⟩at x = [ A , v , x ]
  ... | l ∣ r           = collect l ++ collect r
  ... | _               = []

secretsOfᶜᶠ : Participant → Configuration → Secrets
secretsOfᶜᶠ A = {- Set'.nub ∘-} go
  where
    go : Configuration → Secrets
    go (⟨ B ∶ a ♯ _ ⟩) = if A == B then [ a ] else []
    go (l ∣ r)         = go l ++ go r
    go _               = []

committedParticipants : Configuration → Advertisement → List Participant
committedParticipants (p auth[ (♯▷ ad′) ]) ad = if ad == ad′ then [ p ] else []
committedParticipants (l ∣ r) ad = committedParticipants l ad ++ committedParticipants r ad
committedParticipants _       _  = []

isInitial : Configuration → Bool
isInitial (⟨ _ has _ ⟩at _) = true
isInitial (l ∣ r)           = isInitial l ∧ isInitial r
isInitial _                 = false

Initial : Configuration → Set
Initial = T ∘ isInitial
