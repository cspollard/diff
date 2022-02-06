open import Algebra using (CommutativeRing)

module Algebra.Module.Vec.Recursive {r ℓ} {CR : CommutativeRing r ℓ} where

open CommutativeRing CR

open import Algebra.Module using (Module)
open import Data.Vec.Recursive
open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary using (Rel)
open import Data.Nat using (zero; suc; ℕ)
open import Data.Unit.Polymorphic using (⊤)
open import Assume using (assume)


_^ᴹ_ : ∀ {m ℓm} → Module CR m ℓm → ℕ → Module CR m ℓm
M ^ᴹ n =
  record
  { Carrierᴹ = Carrierᴹ ^ n
  ; _≈ᴹ_ = pointwise _≈ᴹ_
  ; _+ᴹ_ = zipWith _+ᴹ_ n
  ; _*ₗ_ = λ s → map (_*ₗ_ s) n
  ; _*ᵣ_ = λ v s → map (λ x → x *ᵣ s) n v
  ; 0ᴹ = replicate n 0ᴹ
  ; -ᴹ_ = map (-ᴹ_) n
  ; isModule = assume
  }
  where
    open Module M
    open import Data.Unit.Polymorphic

    pointwise : ∀ {a ℓ n} {A : Set a} (~ : Rel A ℓ) → Rel (A ^ n) ℓ
    pointwise {n = ℕ.zero} ~ .tt .tt = ⊤
    pointwise {n = suc ℕ.zero} ~ x y = ~ x y
    pointwise {n = 2+ n} ~ (x , xs) (y , ys) = ~ x y × pointwise ~ xs ys