open import Algebra.Apartness using (HeytingField)

module Data.Real.Abstract.Bundles
  c ℓ₁ ℓ₂ r
  where

open import Relation.Binary using (Rel)
open import Data.Real.Abstract.Structures
open import Level using (_⊔_; suc)

record OrderedHeytingField : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ r)) where
  field
    f : HeytingField c ℓ₁ ℓ₂
  
  open HeytingField f public

  field
    _<_ : Rel Carrier r
    isOrderedHeytingField : IsOrderedHeytingField f _<_

record ArchimedanHeytingField : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ r)) where
  field
    f : HeytingField c ℓ₁ ℓ₂
  
  open HeytingField f public

  field
    _<_ : Rel Carrier r
    isArchimedanHeytingField : IsArchimedanHeytingField f _<_
