module Ring where

open import Real.Base


+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ 
CR.Carrier +-*-commutativeRing = ℝ
CR._≈_ +-*-commutativeRing = _≈_
CR._+_ +-*-commutativeRing = _+_
CR._*_ +-*-commutativeRing = _*_
CR.- +-*-commutativeRing = -_
CR.0# +-*-commutativeRing = 0.0
CR.1# +-*-commutativeRing = 1.0
CR.isCommutativeRing +-*-commutativeRing = todo