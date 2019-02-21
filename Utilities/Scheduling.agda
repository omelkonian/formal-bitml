------------------------------------------------------------------------
-- List-based scheduling.
------------------------------------------------------------------------

module Utilities.Scheduling where

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; Σ; Σ-syntax)
open import Data.List     using (List; []; [_]; _∷_; _++_; map; sum; length)
open import Data.Nat      using (ℕ; _<?_)
open import Data.Fin      using (Fin)
  renaming (zero to fzero; suc to fsuc)

open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Utilities.Lists

module _ {ℓ} {A : Set ℓ} where
  -- Scheduler type.
  Scheduler : Set ℓ
  Scheduler = ∀ (xs : List A)
            → Σ[ ys ∈ List A ]
               Σ[ zs ∈ List A ]
                ( Partition xs (ys , zs)
                -- × Scheduler
                )

alwaysHead : ∀ {ℓ} {A : Set ℓ} → Scheduler {A = A}
alwaysHead []       = []    , [] , Partition-[]
alwaysHead (x ∷ xs) = [ x ] , xs , Partition-L (partition-[]ˡ xs)
