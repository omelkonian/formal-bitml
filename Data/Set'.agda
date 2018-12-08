------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Function      using (_∘_)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Nat      using (ℕ)
open import Data.List     using (List; []; _∷_; [_]; filter; _++_; length)
open import Data.List.Any using (Any; any; here; there)
open import Data.Product  using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction)
open import Relation.Nullary.Decidable            using (True; fromWitness; ⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Data.Set' {A : Set} (_≟_ : Decidable (_≡_ {A = A})) where

  open import Data.List.Membership.DecPropositional _≟_ renaming (_∈_ to _∈′_) public

  ------------------------------------------------------------------------
  -- Decidable equality.

  infix 4 _≟ₗ_
  _≟ₗ_ : Decidable {A = List A} _≡_
  -- xs ≟ₗ ys with xs ≋? ys
  -- ... | no n  = no {!!}
  -- ... | yes y = yes {!!}
  []     ≟ₗ []     = yes refl
  []     ≟ₗ _ ∷ _  = no λ ()
  _ ∷ _  ≟ₗ []     = no λ ()
  x ∷ xs ≟ₗ y ∷ ys with x ≟ y
  ... | no ¬p      = no λ{refl → ¬p refl}
  ... | yes refl   with xs ≟ₗ ys
  ... | no ¬pp     = no λ{refl → ¬pp refl}
  ... | yes refl   = yes refl

  ------------------------------------------------------------------------
  -- Membership.

  ¬? : {P : Set} → Dec P → Dec (¬ P)
  ¬? (yes x) = no (contradiction x)
  ¬? (no ¬x) = yes ¬x

  _∉?_ : Decidable {A = A} _∉_
  x ∉? xs with x ∈? xs
  ... | yes x∈xs = no (λ ¬x∈xs → ¬x∈xs x∈xs)
  ... | no  x∉xs = yes x∉xs


  ------------------------------------------------------------------------
  -- Sublist realtion.
  infix 3 _⊆_
  data _⊆_ : List A → List A → Set where

    base-⊆ : {xsʳ : List A}

             --------
           → [] ⊆ xsʳ

    keep-⊆ : {x : A} {xsˡ xsʳ : List A}

           → xsˡ ⊆ xsʳ
             -------------
           → x ∷ xsˡ ⊆ x ∷ xsʳ

    drop-⊆ : {x : A} {xsˡ xsʳ : List A}

           → xsˡ ⊆ xsʳ
             -------------
           → xsˡ ⊆ x ∷ xsʳ

  infix 3 _⊆?_
  _⊆?_ : List A → List A → Set
  []     ⊆? _ = ⊤
  x ∷ xs ⊆? [] = ⊥
  x ∷ xs ⊆? y ∷ ys with x ≟ y
  ... | yes refl = xs ⊆? ys
  ... | no _     = x ∷ xs ⊆? ys

  sound-⊆ : ∀ {xs ys} {p : xs ⊆? ys} → xs ⊆ ys
  sound-⊆ {[]} {_} {tt} = base-⊆
  sound-⊆ {x ∷ xs} {[]} {()}
  sound-⊆ {x ∷ xs} {y ∷ ys} {pp} with x ≟ y
  ... | yes refl = keep-⊆ (sound-⊆ {p = pp})
  ... | no _     = drop-⊆ (sound-⊆ {p = pp})


  ------------------------------------------------------------------------
  -- Sets as lists with no duplicates.

  noDuplicates : List A → Bool
  noDuplicates [] = true
  noDuplicates (x ∷ xs) with x ∈? xs
  ... | yes _ = false
  ... | no  _ = noDuplicates xs

  Set' : Set
  Set' = ∃[ xs ] T (noDuplicates xs)

  _∈_ : A → Set' → Set
  o ∈ os = o ∈′ proj₁ os

  data ∀∈ (xs : Set') (P : A → Set) : Set where
   mk∀∈ : ∀ (x : A) → (x ∈ xs) → P x → ∀∈ xs P

  infix 2 ∀∈
  syntax ∀∈ xs (λ x → P) = ∀[ x ∈ xs ] P

  data ∃∈ (xs : Set') (P : A → Set) : Set where
   mk∃∈ : ∃[ x ] ((x ∈ xs) × P x) → ∃∈ xs P

  infix 2 ∃∈
  syntax ∃∈ xs (λ x → P) = ∃[ x ∈ xs ] P

  ∅ : Set'
  ∅ = [] , tt

  singleton : A → Set'
  singleton a = [ a ] , tt

  ∣_∣ : Set' → ℕ
  ∣_∣ = length ∘ proj₁

  infixr 5 _─_
  _─_ : Set' → Set' → Set'
  (xs , pxs) ─ (ys , pys) = zs , {!!}
    where
      zs : List A
      zs = filter (λ x → ¬? (x ∈? ys)) xs

  infixr 4 _∪_
  _∪_ : Set' → Set' → Set'
  x@(xs , pxs) ∪ y@(ys , pys) = xs ++ proj₁ z , {!!}
    where
      z : Set'
      z = x ─ y

  fromList : List A → Set'
  fromList [] = [] , tt
  fromList (x ∷ xs) with x ∈? xs
  ... | yes _ = fromList xs
  ... | no  _ = x ∷ proj₁ (fromList xs) , {!!}

  _∺_ : A → Set' → Set'
  x ∺ (xs , _) = fromList (x ∷ xs)

  nodup : List A → List A
  nodup = proj₁ ∘ fromList
