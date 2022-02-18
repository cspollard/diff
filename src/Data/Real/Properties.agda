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

+-*-isArchimedanHeytingField : IsArchimedanHeytingField +-*-heytingField _<_
+-*-isArchimedanHeytingField = assume

abs-isNormedModule : IsNormedModule +-*-module _≤_ abs
abs-isNormedModule = assume

abs-normedModule : NormedModule +-*-commutativeRing _≤_ 0ℓ 0ℓ
abs-normedModule = record { isNormedModule = abs-isNormedModule  }
