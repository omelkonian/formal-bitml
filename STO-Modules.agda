-------------------------------------------------------------------
-- Strict Total Orders for all basic BitML datatypes.
-------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

module STO-Modules where

open import Function            using (const; _on_; _∘_)
open import Level               using (0ℓ)
open import Data.Nat.Properties using ( <-trans; 1+n≰n; <-isStrictTotalOrder
                                      ; <-cmp; <-resp₂-≡ )
open import Data.Nat            using (ℕ; _<_; _>_)
open import Data.Unit           using (⊤)
open import Data.Empty          using (⊥)
open import Data.List           using (List; _∷_)
open import Data.Char as Char
open import Agda.Builtin.Char   using (Char)
  renaming (primCharToNat to →ℕ)
open import Data.String         using ()
  renaming (primStringToList to →[]; primStringFromList to []→)
open import Data.String.Unsafe  using (fromList∘toList)

import Data.AVL.Sets as Sets
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary  using ( StrictTotalOrder; _⇒_; IsEquivalence; _Respects₂_
                                   ; IsStrictTotalOrder; Rel; Transitive; Trichotomous
                                   ; tri≈; tri<; tri> )
import Relation.Binary.Construct.On          as On
import Relation.Binary.PropositionalEquality as Eq
open IsStrictTotalOrder using (compare)
  renaming (trans to sto-trans)

open Eq.≡-Reasoning
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (isEquivalence to ≡-isEquivalence)

import Data.List.Relation.Lex.Strict     as StrictLex
open import Data.List.Relation.Pointwise as Pointwise using (Pointwise)
open import Data.List.Relation.Lex.Core               using (Lex)

open import Utilities.Sets
open import Types

-------------------------------------------------------------------
-- Natural numbers.

STO⟨ℕ⟩ : IsStrictTotalOrder _≡_ _<_
STO⟨ℕ⟩ = <-isStrictTotalOrder

module STO⟦ℕ⟧ = Sets STO⟨ℕ⟩

Set⟨ℕ⟩ : Set
Set⟨ℕ⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦ℕ⟧

-------------------------------------------------------------------
-- Characters, strings, identifiers.

STO⟨Char⟩ : IsStrictTotalOrder _≡_ (_<_ on →ℕ)
STO⟨Char⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = λ {i} {j} {k} i≺j j≺k → ≺-trans {i} {j} {k} i≺j j≺k
         ; compare = ≺-trichotomous
         }

  where
    ≺-trans : Transitive (_<_ on →ℕ)
    ≺-trans {i} {j} {k} i<j j<k = On.transitive →ℕ _<_ <-trans {i} {j} {k} i<j j<k

    -- should be in stdlib
    →ℕ-inj : ∀ {x y} → →ℕ x ≡ →ℕ y → x ≡ y
    →ℕ-inj _ = trustMe
      where open import Relation.Binary.PropositionalEquality.TrustMe

    ≺-trichotomous : Trichotomous _≡_ (_<_ on →ℕ)
    ≺-trichotomous x y with <-cmp (→ℕ x) (→ℕ y)
    ... | tri< a ¬b ¬c = tri< a (λ z → ¬b (cong →ℕ z)) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (→ℕ-inj b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ z → ¬b (cong →ℕ z)) c

_≡ₛ_ : Rel Identifier 0ℓ
_≡ₛ_ = Pointwise (_≡_ on →ℕ) on →[]

_≺ₛ_ : Rel Identifier 0ℓ
_≺ₛ_ = Lex ⊥ (_≡_ on →ℕ) (_<_ on →ℕ) on →[]

STO⟨Identifier⟩′ : IsStrictTotalOrder _≡ₛ_ _≺ₛ_
STO⟨Identifier⟩′ =
  StrictTotalOrder.isStrictTotalOrder
    (On.strictTotalOrder (StrictLex.<-strictTotalOrder Char.strictTotalOrder) →[])

STO⟨Identifier⟩ : IsStrictTotalOrder _≡_ _≺ₛ_
STO⟨Identifier⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = λ {i} {j} {k} → ≺-trans {i} {j} {k}
         ; compare = ≺-trichotomous
         }

  where
    ≺-trans : Transitive _≺ₛ_
    ≺-trans = StrictLex.<-transitive
      (On.isEquivalence →ℕ ≡-isEquivalence)
      (On.respects₂ →ℕ _<_ _≡_ <-resp₂-≡)
      (λ {i} {j} {k} → sto-trans STO⟨Char⟩ {i} {j} {k})

    -- should be in stdlib
    →ℕ-inj : ∀ {x y} → →ℕ x ≡ →ℕ y → x ≡ y
    →ℕ-inj _ = trustMe
      where open import Relation.Binary.PropositionalEquality.TrustMe

    help : _≡ₛ_ ⇒ _≡_
    help {x} {y} pr =
      begin
        x
      ≡⟨ sym (fromList∘toList x) ⟩
        []→ (→[] x)
      ≡⟨ cong []→ (aux pr) ⟩
        []→ (→[] y)
      ≡⟨ fromList∘toList y ⟩
        y
      ∎
      where
        aux : {xs ys : List Char} → Pointwise (_≡_ on →ℕ) xs ys → xs ≡ ys
        aux = Pointwise.rec (λ {xs} {ys} _ → xs ≡ ys) (cong₂ _∷_ ∘ →ℕ-inj) refl

    ≺-trichotomous : Trichotomous _≡_ _≺ₛ_
    ≺-trichotomous x y with compare STO⟨Identifier⟩′ x y
    ... | tri< a ¬b ¬c = tri< a (λ{ refl → ¬c a }) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (help b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ{ refl → ¬a c }) c

module STO⟦Identifier⟧ = Sets STO⟨Identifier⟩

Set⟨Identifier⟩ : Set
Set⟨Identifier⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦Identifier⟧

-------------------------------------------------------------------
-- Participants.

_→ℕₚ : Participant → ℕ
A →ℕₚ = 1
B →ℕₚ = 2

STO⟨Participant⟩ : IsStrictTotalOrder _≡_ (_<_ on _→ℕₚ)
STO⟨Participant⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = ≺-trans
         ; compare = ≺-trichotomous
         }

  where
    ≺-trans : Transitive (_<_ on _→ℕₚ)
    ≺-trans i<j j<k = On.transitive _→ℕₚ _<_ <-trans i<j j<k

    →ℕ-inj : ∀ {x y} → (x →ℕₚ) ≡ (y →ℕₚ) → x ≡ y
    →ℕ-inj {A} {A} x→ℕₚ = refl
    →ℕ-inj {A} {B} ()
    →ℕ-inj {B} {A} ()
    →ℕ-inj {B} {B} x→ℕₚ = refl
    
    ≺-trichotomous : Trichotomous _≡_ (_<_ on _→ℕₚ)
    ≺-trichotomous x y with <-cmp (x →ℕₚ) (y →ℕₚ)
    ... | tri< a ¬b ¬c = tri< a (λ z → ¬b (cong _→ℕₚ z)) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (→ℕ-inj b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ z → ¬b (cong _→ℕₚ z)) c  

module STO⟦Participant⟧ = Sets STO⟨Participant⟩

Set⟨Participant⟩ : Set
Set⟨Participant⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦Participant⟧

-------------------------------------------------------------------
-- Preconditions.

postulate
  _≺ₚ_ : Rel Precondition 0ℓ
STO⟨Precondition⟩ : IsStrictTotalOrder _≡_ _≺ₚ_
STO⟨Precondition⟩ = {!!}

module STO⟦Precondition⟧ = Sets STO⟨Precondition⟩

Set⟨Precondition⟩ : Set
Set⟨Precondition⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦Precondition⟧
