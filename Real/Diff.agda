module Real.Diff where

import Real.Base as R
open R using (ℝ)
open import Real.Order public

import Data.Fin as F
open F using (Fin)


open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Structures using (IsModule)
open import Algebra.Module.Bundles using (Module)
open import Algebra.Module.Normed using (IsNormedModule; NormedModule; tensorUnit; directProduct)
open import Assume using (assume)
open import Level using (0ℓ)

import Algebra.Module.Construct.Zero as Z
import Algebra.Module.Construct.DirectProduct as DP
import Algebra.Module.Construct.TensorUnit as U

open import Algebra.Module.Diff
import Data.Nat as ℕ
open ℕ using (ℕ)
open import Data.Unit.Polymorphic using (tt; ⊤)
open import Data.Product using (_×_; _,_; proj₁)
open import Algebra.Module using (Module)
open import Algebra.Module.Morphism.Module
open import Algebra.Module.Vec.Recursive

module M = Module
module CR = CommutativeRing





instance
  ℝ-isCommutativeRing : IsCommutativeRing ℝ._≈_ ℝ._+_ ℝ._*_ ℝ.-_ 0.0 1.0
  ℝ-isCommutativeRing = assume

  ℝ-commutativeRing ℝ-cr : CommutativeRing 0ℓ 0ℓ
  ℝ-commutativeRing = record { isCommutativeRing = ℝ-isCommutativeRing }
  ℝ-cr = ℝ-commutativeRing

  ℝ-mod : Module ℝ-cr 0ℓ 0ℓ
  ℝ-mod = U.⟨module⟩

module Mod = Module
open Module {{...}}


abs : ℝ → ℝ
abs x = if does (0.0 ≤? x) then x else ℝ.- x
  where
    open import Data.Bool using (if_then_else_)
    open import Relation.Nullary using (does)


DRR : Set _
DRR = D ℝ-mod ℝ-mod

instance
  ℝ^n : ∀ {n} → Module ℝ-commutativeRing 0ℓ 0ℓ
  ℝ^n {n} = ℝ-mod ^ᴹ n


_>-<_ : ∀ {ma ℓma} {MA : Module ℝ-cr ma ℓma} (f df : ℝ → ℝ) → D MA ℝ-mod → D MA ℝ-mod
f >-< df = λ g → flip compose g λ x → (f x , (λ dx → df x ℝ.* dx) , assume)
  where open import Function

infixl 7 _÷_

-- linear and bilinear forms
_+_ _*_ _÷_ : (x y : DRR) → D (ℝ-mod ^ᴹ 2) ℝ-mod
x + y =
  λ (z1 , z2) →
    let (xz , dxz) = x z1
        (yz , dyz) = y z2
    in xz ℝ.+ yz , (λ where (dx , dy) → proj₁ dxz dx ℝ.+ proj₁ dyz dy) , assume

x * y =
  λ (z1 , z2) →
    let (xz , dxz) = x z1
        (yz , dyz) = y z2
    in xz ℝ.+ yz , (λ where (dx , dy) → xz ℝ.* proj₁ dyz dy ℝ.+ proj₁ dxz dx ℝ.* yz) , assume
    
dup
  : ∀ {r ℓ} {CR : CommutativeRing r ℓ}
  → ∀ {m ℓm} {M : Module CR m ℓm}
  → ∀ {n} → Mod.Carrierᴹ M → Mod.Carrierᴹ (M ^ᴹ n)
dup = {!   !}

infixr 9 e^_
log e^_ sin cos tan sinh cosh tanh recip
  : ∀ {ma ℓma} {MA : Module ℝ-cr ma ℓma} → D MA ℝ-mod → D MA ℝ-mod
log = ℝ.log >-< λ x → 1.0 ℝ.÷ x
-- TODO
-- this could have sharing and be more efficient.
e^_ = ℝ.e^_ >-< ℝ.e^_
recip x = e^ (-ᴹ log x)
f ÷ g = f * recip g
sin = ℝ.sin >-< ℝ.cos
cos = ℝ.cos >-< λ x → ℝ.- ℝ.sin x
tan x = {!   !}
-- TODO
-- maybe could be more efficient using exponentials?
sinh = ℝ.sinh >-< ℝ.cosh
cosh = ℝ.cosh >-< ℝ.sinh
tanh x = {!   !}



infixl 8 _**_
_**_ : DRR → DRR → D (ℝ-mod ^ᴹ 2) ℝ-mod
f ** g = e^ (g * log f)

const : ℝ → D (ℝ-mod ^ᴹ 0) ℝ-mod
const x tt = x , (λ _ → 0.0) , assume

-- module _ where
--   open import Relation.Binary.PropositionalEquality
--   equal : (n : ℕ) → Carrierᴹ (ℝ^ n) ≡ Vec ℝ n
--   equal ℕ.zero = refl
--   equal 1 = refl
--   equal 2 = refl
--   equal 3 = refl
--   equal (ℕ.suc n) = cong (ℝ ×_) (equal n)

-- -- fins : ∀ {n} → Vec (Fin n) n
-- -- fins = {!   !}


-- -- descend
-- --   : ∀ {n} → (f : D (ℝ^ n) ℝ-cr) (x lr : Carrierᴹ (ℝ^ n)) → Carrierᴹ (ℝ^ n)
-- -- descend {n} f x lr = 
-- --   let (fx , dfx , _) = f x
-- --       Δ = zipWith (λ i dx → lookup i ?) fins lr
-- --   in {! Δ !}
-- --   where
-- --     import Data.Fin as F

-- --     open Module
-- --     open CommutativeRing ℝ-commutativeRing

-- --     zipWith
-- --       : ∀ {n a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
-- --       → Vec A n → Vec B n → Vec C n
-- --     zipWith {n = ℕ.zero} {c = c} f _ _ = tt
-- --     zipWith {ℕ.suc n} f (x , xs) (y , ys) = f x y , zipWith f xs ys

-- --     map : ∀ {n a b} {A : Set a} {B : Set b} (f : A → B) → Vec A n → Vec B n
-- --     map {ℕ.zero} f _ = tt
-- --     map {ℕ.suc n} f (x , xs) = f x , map f xs


-- -- module Tests where
-- --   open import Relation.Binary.PropositionalEquality
-- --   _ : run (e^ const 2.0) (tt {0ℓ}) ≈ (ℝ.e^ 2.0)
-- --   _ = refl


-- -- -- already have composition. what is left?!




-- -- -- -- -- asdf : D ℝ-cr ℝ-cr
-- -- -- -- -- asdf = 2* +ᴹ exp

-- -- -- -- -- open import Relation.Binary.PropositionalEquality using (refl)

-- -- -- -- -- _ : run asdf 2.0 ≈ (2.0 * 2.0 + e^ 2.0)
-- -- -- -- -- _ = refl

-- -- -- -- -- asdf' : ℝ → ℝ → ℝ
-- -- -- -- -- asdf' x dx = ∇ asdf [ x ]∙ dx

-- -- -- -- -- _ : ∀ x dx → asdf' x dx ≈ (2.0 * x * dx + (e^ x) * dx)
-- -- -- -- -- _ = λ x dx → refl



-- -- -- -- -- -- _ : D ℝ-cr ℝ-cr
-- -- -- -- -- -- _ = test +ᴹ exp



-- -- -- -- -- -- exp {m = ℕ.suc n} (v , vs) = e^ v , exp {m = n} vs

-- -- -- -- -- -- ℝ-isNormedModule : IsNormedModule ℝ-cr _≤_ abs
-- -- -- -- -- -- ℝ-isNormedModule = assume

-- -- -- -- -- -- ℝ-normedModule : NormedModule ℝ-commutativeRing _≤_ 0ℓ 0ℓ
-- -- -- -- -- -- ℝ-normedModule = record { isNormedModule = ℝ-isNormedModule }


-- -- -- -- -- -- open import Data.Nat using (ℕ; suc; zero)

-- -- -- -- -- -- ℝ^_-normedModule : ℕ → NormedModule ℝ-commutativeRing _≤_ 0ℓ 0ℓ
-- -- -- -- -- -- ℝ^ zero -normedModule = Normed.tensorUnit abs
-- -- -- -- -- -- ℝ^ suc n -normedModule = Normed.directProduct (Normed.tensorUnit abs) (ℝ^ n -normedModule)

-- -- -- -- -- -- open import Algebra.Module.Limit ℝ-normedModule ℝ-normedModule hiding (D[_,_][_,_])
-- -- -- -- -- -- open import Algebra.Module.Limit using (D[_,_][_,_])
-- -- -- -- -- -- open import Data.Float using (e^_)
-- -- -- -- -- -- open import Data.Product using (_,_)

-- -- -- -- -- -- e^-differentiable : Differentiable e^_
-- -- -- -- -- -- e^-differentiable = λ x → (λ dy → e^ x * dy) , assume

-- -- -- -- -- -- a*x-differentiable : ∀ a → Differentiable (λ x → a * x)
-- -- -- -- -- -- a*x-differentiable a = λ x → (λ dy → a * dy) , assume


-- -- -- -- -- -- open import Compose ℝ-normedModule ℝ-normedModule ℝ-normedModule
-- -- -- -- -- -- open import Function using (_∘_)

-- -- -- -- -- -- e^2x-differentiable : ∀ x → D[ ℝ-normedModule , ℝ-normedModule ][ (e^_ ∘ (2.0 *_)) , x ]
-- -- -- -- -- -- e^2x-differentiable = ∘-differentiable {e^_} {2.0 *_} e^-differentiable (a*x-differentiable 2.0)

-- -- -- -- -- -- asdf' : ℝ → ℝ → ℝ
-- -- -- -- -- -- asdf' x dx = proj₁ (a*x-differentiable 2.0 x) dx
-- -- -- -- -- --   where open import Data.Product



-- -- -- -- -- -- -- asdf : ℝ → ℝ
-- -- -- -- -- -- -- asdf x = proj₁ (e^2x-differentiable x)
-- -- -- -- -- -- --   where open import Data.Product

-- -- -- -- -- -- -- TODO
-- -- -- -- -- -- -- Can apply ModuleHomomorphism to NormedModule?