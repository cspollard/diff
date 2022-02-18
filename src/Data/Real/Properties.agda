module Data.Real.Properties where

open import Data.Real.Base as ℝ
open import Data.Real.Order
open import Data.Real.Abstract.Structures
  using (IsOrderedHeytingField; IsArchimedanHeytingField)
open import Assume
open import Algebra using (IsCommutativeRing; CommutativeRing)
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Normed using (IsNormedModule; NormedModule)
open import Algebra.Apartness using (IsHeytingField; HeytingField)
open import Level using (0ℓ)
open import Data.Product using (_,_)


+-*-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0.0 1.0
+-*-isCommutativeRing = assume

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record { isCommutativeRing = +-*-isCommutativeRing }

+-*-module : Module +-*-commutativeRing 0ℓ 0ℓ
+-*-module = ⟨module⟩

+-*-isHeytingField : IsHeytingField _≈_ _≉_ _+_ _*_ -_ 0.0 1.0
+-*-isHeytingField = assume

+-*-heytingField : HeytingField 0ℓ 0ℓ 0ℓ
+-*-heytingField = record { isHeytingField = +-*-isHeytingField  }

+-*-isOrderedHeytingField : IsOrderedHeytingField +-*-heytingField _<_
+-*-isOrderedHeytingField =
  record
  { isStrictTotalOrder = <-isStrictTotalOrder
  ; ordered = assume
  }

+-*-isArchimedanHeytingField : IsArchimedanHeytingField +-*-heytingField _<_
+-*-isArchimedanHeytingField =
  record
  { dense = λ a b a<b → ((a + b) ÷ 2.0) , assume
  ; archimedan = λ a b a<0 b<0 → ∣ unsafeM ⌈ b ÷ a ⌉ ∣ , assume
  }
  where
    open import Data.Integer using (∣_∣)
    open import Data.Maybe

    unsafeM : ∀ {a} {A : Set a} → Maybe A → A
    unsafeM (just x) = x
    unsafeM nothing = assume

abs-isNormedModule : IsNormedModule +-*-module _≤_ abs
abs-isNormedModule = assume

abs-normedModule : NormedModule +-*-commutativeRing _≤_ 0ℓ 0ℓ
abs-normedModule = record { isNormedModule = abs-isNormedModule  }
