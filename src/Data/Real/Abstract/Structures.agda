open import Algebra.Apartness using (HeytingField)

module Data.Real.Abstract.Structures {c ℓ₁ ℓ₂} (f : HeytingField c ℓ₁ ℓ₂) where

open HeytingField f

open import Relation.Binary using (Rel; IsStrictTotalOrder)
open import Level using (_⊔_)
open import Data.Product using (_×_; ∃-syntax)

import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)

record IsOrderedHeytingField
  {r} (_<_ : Rel Carrier r) : Set (c ⊔ ℓ₁ ⊔ r)
  where

  field
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_
    ordered : ∀ a b c → a < b → (a + c) < (b + c) × (c + a) < (c + b)
    

_ℕ*_ : ℕ → Carrier → Carrier
zero ℕ* x = 1#
suc n ℕ* x = x * (n ℕ* x)

record IsArchimedanHeytingField
  {r} (_<_ : Rel Carrier r) : Set (c ⊔ ℓ₁ ⊔ r)
  where

  field
    dense : ∀ a b → a < b → ∃[ c ] (a < c) × (c < b)
    archimedan : ∀ a b → 0# < a → 0# < b → ∃[ n ] (b < (n ℕ* a))
