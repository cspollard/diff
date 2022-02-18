module Data.Real.Order where

open import Assume
open import Data.Real.Base
open import Data.Bool using (T; T?)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary
  using (IsDecTotalOrder; DecTotalOrder; IsApartnessRelation; ApartnessRelation; Rel)
open import Level using (0ℓ)

_≤_ : ℝ → ℝ → Set
x ≤ y = T (x ≤ᵇ y)

open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ public using (_<_)

_≤?_ : ∀ x y → Dec (x ≤ y)
x ≤? y = T? (x ≤ᵇ y)

≤-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_
≤-isDecTotalOrder = record { isTotalOrder = assume ; _≟_ = _≈?_ ; _≤?_ = _≤?_ }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record { isDecTotalOrder = ≤-isDecTotalOrder }

abs : ℝ → ℝ
abs x = if does (0.0 ≤? x) then x else - x
  where
    open import Data.Bool using (if_then_else_)
    open import Relation.Nullary using (does)

-- TODO
-- should this move to Data.Real.Equality?
_≉_ : Rel ℝ 0ℓ
x ≉ y = ¬ x ≈ y

≉-isApartnessRelation : IsApartnessRelation _≈_ _≉_
≉-isApartnessRelation = assume

≉-apartnessRelation : ApartnessRelation 0ℓ 0ℓ 0ℓ
≉-apartnessRelation = record { isApartnessRelation = ≉-isApartnessRelation }
