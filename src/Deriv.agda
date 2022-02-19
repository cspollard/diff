module Deriv where

open import Relation.Binary.Bundles using (DecSetoid)
open import Algebra.Bundles using (Semiring)
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no)

module _ (S : DecSetoid 0ℓ 0ℓ) (Targ : Set) where

  open DecSetoid S renaming (Carrier to Key)


  infixl 6 _+_
  infixl 7 _*_
  data Expr : Set where
    ↑ : Targ → Expr
    ! : Key → Expr
    _+_ : Expr → Expr → Expr
    _*_ : Expr → Expr → Expr
 

module _ {S : DecSetoid 0ℓ 0ℓ} (R : Semiring 0ℓ 0ℓ) where

  private module S = DecSetoid S
  open S renaming (Carrier to Key)
  private module R = Semiring R
  open R using (0#; 1#) renaming (Carrier to Targ)

  eval
    : (lookup : Key → Targ)
    → (expr : Expr S Targ)
    → Targ
  eval lookup (↑ x) = x
  eval lookup (! x) = lookup x
  eval lookup (x + x₁) = eval lookup x₁ R.+ eval lookup x₁
  eval lookup (x * x₁) = eval lookup x₁ R.* eval lookup x₁


  deriv : Expr S Targ → Key → Expr S Targ
  deriv (↑ x) k = ↑ 0#
  deriv (! x) k with x ≟ k
  deriv (! x) k | yes _ = ↑ 1#
  deriv (! x) k | no _ = ↑ 0#
  deriv (e + e₁) k = deriv e k + deriv e₁ k
  deriv (e * e₁) k = (deriv e k * e₁) + (e * deriv e₁ k)


open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (+-*-semiring)
open import Data.String
open import Relation.Binary.PropositionalEquality using (decSetoid)

asdf : Expr (decSetoid _≟_) ℕ
asdf = ↑ 2 + (↑ 5 * (! "hello" * ! "goodbye"))

asdf' : Expr (decSetoid _≟_) ℕ
asdf' = deriv +-*-semiring asdf "hello"

normalize : ∀ {D} → Expr D ℕ → Expr D ℕ
normalize (x + y) with normalize x | normalize y
normalize (x + y) | ↑ w | ↑ z   = ↑ (w Data.Nat.+ z)
normalize (x + y) | ↑ 0 | z   = z
normalize (x + y) | w   | ↑ 0 = w
normalize (x + y) | w   | z   = w + z
normalize (x * y) with normalize x | normalize y
normalize (x * y) | ↑ w | ↑ z   = ↑ (w Data.Nat.* z)
normalize (x * y) | ↑ 0 | z   = ↑ 0
normalize (x * y) | w   | ↑ 0 = ↑ 0
normalize (x * y) | ↑ 1 | z   = z
normalize (x * y) | w   | ↑ 1 = w
normalize (x * y) | w   | z   = w * z
normalize z = z

module _ (R : Semiring 0ℓ 0ℓ) where
  open Semiring R
  private module R = Semiring R

  asdf'' : Carrier
  asdf'' = 1# R.+ 0#