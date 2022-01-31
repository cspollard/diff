module Real.Base where

import Data.Float

module ℝ = Data.Float

open ℝ using (_+_; _*_; -_; _≈_; _≈?_) renaming (Float to ℝ) public