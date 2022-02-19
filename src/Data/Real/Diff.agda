module Data.Real.Diff where

import Data.Real as ℝ
open ℝ using (ℝ)
open import Data.Real.Order
open import Data.Real.Properties

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

-- open import Algebra.Module.Diff
import Data.Nat as ℕ
open ℕ using (ℕ)
open import Data.Unit.Polymorphic using (tt; ⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Algebra.Module using (Module)
open import Algebra.Module.Morphism.Module
open import Algebra.Module.Vec.Recursive


open import Relation.Binary.PropositionalEquality
open import Data.Product.Properties using (×-≡,≡→≡)
open ≡-Reasoning

instance
  ℝ-cr : CommutativeRing 0ℓ 0ℓ
  ℝ-cr = ℝ-commutativeRing

  ℝ-mod : Module ℝ-cr 0ℓ 0ℓ
  ℝ-mod = ℝ-module

module Mod = Module
open Module {{...}}

open import Data.Vec.Recursive using (_^_)

D : ℕ → Set
D ℕ.zero = ℝ
D (ℕ.suc n) = ℝ × D n

mutual
  const : ∀ {n} → ℝ → D n
  const {ℕ.zero} x = x
  const {ℕ.suc n} x = x , zero

  zero : ∀ {n} → D n
  zero = const 0.0

diff : ∀ {n} → D (ℕ.suc n) → D n
diff = proj₂

return : ∀ {n} → ℝ → D n
return {ℕ.zero} x = x
return {ℕ.suc n} x = x , const 1.0

lop : ∀ {n} → D (ℕ.suc n) → D n
lop {ℕ.zero} (f , f') = f
lop {ℕ.suc n} (f , f') = f , lop f'

lop-zero : ∀ {n} → lop zero ≡ zero {n}
lop-zero {ℕ.zero} = refl
lop-zero {ℕ.suc n} = ×-≡,≡→≡ (refl , lop-zero)

lop-const : ∀ {n} x → lop (const x) ≡ const {n} x
lop-const {ℕ.zero} x = refl
lop-const {ℕ.suc n} x = ×-≡,≡→≡ (refl , lop-zero)

infixl 6 _+_
infixl 7 _*_

_*_ _+_ : ∀ {n} (x y : D n) → D n

_*_ {ℕ.zero} x y = x ℝ.* y
_*_ {ℕ.suc n} ff@(f , f') gg@(g , g') = f * g , lop ff * g' + lop gg * f'

_+_ {ℕ.zero} x y = x ℝ.+ y
_+_ {ℕ.suc n} (f , f') (g , g') = f + g , f' + g'


build : ∀ {n} → (ℝ → ℝ) → (∀ {m} → ℝ → D m) → ℝ → D n
build {ℕ.zero} f g x = f x
build {ℕ.suc n} f g x = f x , g x

e^_ : ∀ {n} → ℝ → D n
e^_ {ℕ.zero} x = ℝ.e^ x
e^_ {ℕ.suc n} x = e^ x , e^ x

infix 8 _^^_
_^^_ : ∀ {n} → ℝ → ℕ → D n
_^^_ x (ℕ.suc m) = return x * x ^^ m
_^^_ x ℕ.zero = const 1.0

infix 2 _!_
_!_ : (∀ {n} → D n) → ∀ m → D m 
d ! m = d {m}

-- TODO should move to _≈_ at some point

+-identity : ∀ {n} (x : D n) → x + zero ≡ x
+-identity {ℕ.zero} x = assume
+-identity {ℕ.suc n} (x , x') = ×-≡,≡→≡ (+-identity x , +-identity x')

*-commutative : ∀ {n} {x y : D n} → x * y ≡ y * x
*-commutative = assume

*-zero : ∀ {n} (x : D n) → x * zero ≡ zero
*-zero {ℕ.zero} x = assume
*-zero {ℕ.suc n} xx@(x , x') = ×-≡,≡→≡ (*-zero x , proof)
  where
    open ≡-Reasoning

    proof : lop xx * diff zero + lop zero * x' ≡ zero
    proof =
      begin
        lop xx * diff zero + lop zero * x'
      ≡⟨ cong₂ _+_ (*-zero (lop xx)) (cong₂ _*_ lop-zero refl) ⟩
        zero + zero * x'
      ≡⟨ cong₂ _+_ refl *-commutative ⟩
        zero + x' * zero
      ≡⟨ cong₂ _+_ refl (*-zero x') ⟩
        zero + zero
      ≡⟨ +-identity zero ⟩
        zero
      ∎


*-identity : ∀ {n} (x : D n) → (const 1.0 * x) ≡ x
*-identity {ℕ.zero} x = assume
*-identity {ℕ.suc n} xx@(x , x') = ×-≡,≡→≡ (*-identity x , proof)
  where
    open ≡-Reasoning

    lopconst≡const : ∀ {m} x → lop {m} (const x) ≡ const x
    lopconst≡const {ℕ.zero} _ = refl
    lopconst≡const {ℕ.suc m} x = ×-≡,≡→≡ (refl , lopconst≡const 0.0)

    proof : lop (1.0 , zero) * x' + lop xx * zero ≡ x'
    proof =
      begin
        lop (1.0 , zero) * x' + lop xx * zero
      ≡⟨ cong₂ _+_ refl (*-zero (lop xx)) ⟩
        lop (1.0 , zero) * x' + zero
      ≡⟨ +-identity (lop (1.0 , zero) * x') ⟩
        lop (1.0 , zero) * x'
      ≡⟨ cong₂ _*_ (lop-const 1.0) refl ⟩
        const 1.0 * x'
      ≡⟨ *-identity x' ⟩
        x'
      ∎

_>>=_ : ∀ {n} → D n → (ℝ → D n) → D n
_>>=_ {ℕ.zero} x f = f x
_>>=_ {ℕ.suc n} (g , g') f =
  let (fg , f'g) = f g
  in fg , f'g * g'

liftD : ∀ {n} → (ℝ → D n) → D n → D n
liftD f d = d >>= f


asdf : ∀ n → ℝ → D n
asdf n x = do
  y ← x ^^ 2
  z ← y ^^ 2
  -- z ← e^ y
  return z



-- DRR : Set _
-- DRR = D ℝ-mod ℝ-mod

-- instance
--   ℝ^n : ∀ {n} → Module ℝ-commutativeRing 0ℓ 0ℓ
--   ℝ^n {n} = ℝ-mod ^ᴹ n


-- _>-<_ : ∀ {ma ℓma} {MA : Module ℝ-cr ma ℓma} (f df : ℝ → ℝ) → D MA ℝ-mod → D MA ℝ-mod
-- f >-< df = λ g → flip compose g λ x → (f x , (λ dx → df x ℝ.* dx) , assume)
--   where open import Function

-- infixl 7 _÷_

-- -- linear and bilinear forms
-- _+_ _*_ _÷_ : (x y : DRR) → D (ℝ-mod ^ᴹ 2) ℝ-mod
-- x + y =
--   λ (z1 , z2) →
--     let (xz , dxz) = x z1
--         (yz , dyz) = y z2
--     in xz ℝ.+ yz , (λ where (dx , dy) → proj₁ dxz dx ℝ.+ proj₁ dyz dy) , assume

-- x * y =
--   λ (z1 , z2) →
--     let (xz , dxz) = x z1
--         (yz , dyz) = y z2
--     in xz ℝ.+ yz , (λ where (dx , dy) → xz ℝ.* proj₁ dyz dy ℝ.+ proj₁ dxz dx ℝ.* yz) , assume
    
-- dup
--   : ∀ {r ℓ} {CR : CommutativeRing r ℓ}
--   → ∀ {m ℓm} {M : Module CR m ℓm}
--   → ∀ {n} → Mod.Carrierᴹ M → Mod.Carrierᴹ (M ^ᴹ n)
-- dup = {!   !}

-- infixr 9 e^_
-- log e^_ sin cos tan sinh cosh tanh recip
--   : ∀ {ma ℓma} {MA : Module ℝ-cr ma ℓma} → D MA ℝ-mod → D MA ℝ-mod
-- log = ℝ.log >-< λ x → 1.0 ℝ.÷ x
-- -- TODO
-- -- this could have sharing and be more efficient.
-- e^_ = ℝ.e^_ >-< ℝ.e^_
-- recip x = e^ (-ᴹ log x)
-- f ÷ g = f * recip g
-- sin = ℝ.sin >-< ℝ.cos
-- cos = ℝ.cos >-< λ x → ℝ.- ℝ.sin x
-- tan x = {!   !}
-- -- TODO
-- -- maybe could be more efficient using exponentials?
-- sinh = ℝ.sinh >-< ℝ.cosh
-- cosh = ℝ.cosh >-< ℝ.sinh
-- tanh x = {!   !}



-- infixl 8 _**_
-- _**_ : DRR → DRR → D (ℝ-mod ^ᴹ 2) ℝ-mod
-- f ** g = e^ (g * log f)

-- const : ℝ → D (ℝ-mod ^ᴹ 0) ℝ-mod
-- const x tt = x , (λ _ → 0.0) , assume

-- -- module _ where
-- --   open import Relation.Binary.PropositionalEquality
-- --   equal : (n : ℕ) → Carrierᴹ (ℝ^ n) ≡ Vec ℝ n
-- --   equal ℕ.zero = refl
-- --   equal 1 = refl
-- --   equal 2 = refl
-- --   equal 3 = refl
-- --   equal (ℕ.suc n) = cong (ℝ ×_) (equal n)

-- -- -- fins : ∀ {n} → Vec (Fin n) n
-- -- -- fins = {!   !}


-- -- -- descend
-- -- --   : ∀ {n} → (f : D (ℝ^ n) ℝ-cr) (x lr : Carrierᴹ (ℝ^ n)) → Carrierᴹ (ℝ^ n)
-- -- -- descend {n} f x lr = 
-- -- --   let (fx , dfx , _) = f x
-- -- --       Δ = zipWith (λ i dx → lookup i ?) fins lr
-- -- --   in {! Δ !}
-- -- --   where
-- -- --     import Data.Fin as F

-- -- --     open Module
-- -- --     open CommutativeRing ℝ-commutativeRing

-- -- --     zipWith
-- -- --       : ∀ {n a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
-- -- --       → Vec A n → Vec B n → Vec C n
-- -- --     zipWith {n = ℕ.zero} {c = c} f _ _ = tt
-- -- --     zipWith {ℕ.suc n} f (x , xs) (y , ys) = f x y , zipWith f xs ys

-- -- --     map : ∀ {n a b} {A : Set a} {B : Set b} (f : A → B) → Vec A n → Vec B n
-- -- --     map {ℕ.zero} f _ = tt
-- -- --     map {ℕ.suc n} f (x , xs) = f x , map f xs


-- -- -- module Tests where
-- -- --   open import Relation.Binary.PropositionalEquality
-- -- --   _ : run (e^ const 2.0) (tt {0ℓ}) ≈ (ℝ.e^ 2.0)
-- -- --   _ = refl


-- -- -- -- already have composition. what is left?!




-- -- -- -- -- -- asdf : D ℝ-cr ℝ-cr
-- -- -- -- -- -- asdf = 2* +ᴹ exp

-- -- -- -- -- -- open import Relation.Binary.PropositionalEquality using (refl)

-- -- -- -- -- -- _ : run asdf 2.0 ≈ (2.0 * 2.0 + e^ 2.0)
-- -- -- -- -- -- _ = refl

-- -- -- -- -- -- asdf' : ℝ → ℝ → ℝ
-- -- -- -- -- -- asdf' x dx = ∇ asdf [ x ]∙ dx

-- -- -- -- -- -- _ : ∀ x dx → asdf' x dx ≈ (2.0 * x * dx + (e^ x) * dx)
-- -- -- -- -- -- _ = λ x dx → refl



-- -- -- -- -- -- -- _ : D ℝ-cr ℝ-cr
-- -- -- -- -- -- -- _ = test +ᴹ exp



-- -- -- -- -- -- -- exp {m = ℕ.suc n} (v , vs) = e^ v , exp {m = n} vs

-- -- -- -- -- -- -- ℝ-isNormedModule : IsNormedModule ℝ-cr _≤_ abs
-- -- -- -- -- -- -- ℝ-isNormedModule = assume

-- -- -- -- -- -- -- ℝ-normedModule : NormedModule ℝ-commutativeRing _≤_ 0ℓ 0ℓ
-- -- -- -- -- -- -- ℝ-normedModule = record { isNormedModule = ℝ-isNormedModule }


-- -- -- -- -- -- -- open import Data.Nat using (ℕ; suc; zero)

-- -- -- -- -- -- -- ℝ^_-normedModule : ℕ → NormedModule ℝ-commutativeRing _≤_ 0ℓ 0ℓ
-- -- -- -- -- -- -- ℝ^ zero -normedModule = Normed.tensorUnit abs
-- -- -- -- -- -- -- ℝ^ suc n -normedModule = Normed.directProduct (Normed.tensorUnit abs) (ℝ^ n -normedModule)

-- -- -- -- -- -- -- open import Algebra.Module.Limit ℝ-normedModule ℝ-normedModule hiding (D[_,_][_,_])
-- -- -- -- -- -- -- open import Algebra.Module.Limit using (D[_,_][_,_])
-- -- -- -- -- -- -- open import Data.Float using (e^_)
-- -- -- -- -- -- -- open import Data.Product using (_,_)

-- -- -- -- -- -- -- e^-differentiable : Differentiable e^_
-- -- -- -- -- -- -- e^-differentiable = λ x → (λ dy → e^ x * dy) , assume

-- -- -- -- -- -- -- a*x-differentiable : ∀ a → Differentiable (λ x → a * x)
-- -- -- -- -- -- -- a*x-differentiable a = λ x → (λ dy → a * dy) , assume


-- -- -- -- -- -- -- open import Compose ℝ-normedModule ℝ-normedModule ℝ-normedModule
-- -- -- -- -- -- -- open import Function using (_∘_)

-- -- -- -- -- -- -- e^2x-differentiable : ∀ x → D[ ℝ-normedModule , ℝ-normedModule ][ (e^_ ∘ (2.0 *_)) , x ]
-- -- -- -- -- -- -- e^2x-differentiable = ∘-differentiable {e^_} {2.0 *_} e^-differentiable (a*x-differentiable 2.0)

-- -- -- -- -- -- -- asdf' : ℝ → ℝ → ℝ
-- -- -- -- -- -- -- asdf' x dx = proj₁ (a*x-differentiable 2.0 x) dx
-- -- -- -- -- -- --   where open import Data.Product



-- -- -- -- -- -- -- -- asdf : ℝ → ℝ
-- -- -- -- -- -- -- -- asdf x = proj₁ (e^2x-differentiable x)
-- -- -- -- -- -- -- --   where open import Data.Product

-- -- -- -- -- -- -- -- TODO
-- -- -- -- -- -- -- -- Can apply ModuleHomomorphism to NormedModule?