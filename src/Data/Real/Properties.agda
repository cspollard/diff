module Data.Real.Properties where

open import Data.Real.Base as ℝ
open import Data.Real.Order
open import Assume
open import Algebra using (IsCommutativeRing; CommutativeRing)
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Normed using (IsNormedModule; NormedModule)
open import Level using (0ℓ)


+-*-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0.0 1.0
+-*-isCommutativeRing = assume

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record { isCommutativeRing = +-*-isCommutativeRing }

+-*-module : Module +-*-commutativeRing 0ℓ 0ℓ
+-*-module = ⟨module⟩

abs-isNormedModule : IsNormedModule +-*-module _≤_ abs
abs-isNormedModule = assume

abs-normedMordule : NormedModule +-*-commutativeRing _≤_ 0ℓ 0ℓ
abs-normedMordule = record { isNormedModule = abs-isNormedModule  }

