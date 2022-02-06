{-# OPTIONS --allow-unsolved-metas #-}

module Real-Backup where

open import Data.Float hiding (_-_; _≈_)
open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Bundles using (Module)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Data.Sum using (_⊎_; inj₁; inj₂)
module CR = CommutativeRing
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning)
open import Algebra.Module.Construct.TensorUnit
import Limit
open import InnerProduct
open import Relation.Nullary using (¬_)



private postulate
  todo : ∀ {a} {A : Set a} → A

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ 
CR.Carrier +-*-commutativeRing = Float
CR._≈_ +-*-commutativeRing = _≡_
CR._+_ +-*-commutativeRing = _+_
CR._*_ +-*-commutativeRing = _*_
CR.- +-*-commutativeRing = -_
CR.0# +-*-commutativeRing = 0.0
CR.1# +-*-commutativeRing = 1.0
CR.isCommutativeRing +-*-commutativeRing = todo

+-*-module : Module +-*-commutativeRing 0ℓ 0ℓ
+-*-module = ⟨module⟩

<-strictTotalOrder : StrictTotalOrder _ 0ℓ 0ℓ
<-strictTotalOrder = record { Carrier = Float; _≈_ = _≡_; _<_ = todo; isStrictTotalOrder = todo }

infixl 6 _-_
_-_ : Float → Float → Float
x - y = x + (- y)

open StrictTotalOrder <-strictTotalOrder


+-*-isInnerProduct : IsInnerProduct isStrictTotalOrder (λ x → x) +-*-module _*_
+-*-isInnerProduct = todo

+-*-isNormed : IsNormed isStrictTotalOrder (λ x → x) +-*-module _*_ sqrt
+-*-isNormed =
  record
  { isInnerProduct = +-*-isInnerProduct
  ; sqrt-law = todo
  ; sqrt-concave = todo
  ; sqrt-cong = todo
  }

module _ where

  open Limit +-*-isNormed +-*-isNormed
  open IsNormed +-*-isNormed
  open Module +-*-module
  open CommutativeRing +-*-commutativeRing using (refl; +-cong)
  open import Data.Product
  open import Algebra.Module.Morphism.Structures

  _ : ∀ c → (c + x) ⟶ c as x ⟶0
  _ = λ c ε (0<ε) → ε , λ x (0<x , x<ε) →
    begin-strict
      ∥ c + x - c ∥
    ≈⟨ ∥∥-cong (y+x-y≈x c x) ⟩
      ∥ x ∥
    <⟨ x<ε ⟩
      ε
    ∎
    where
      open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

      y+x-y≈x : ∀ y x → y + x - y ≈ᴹ x
      y+x-y≈x y x = 
        begin-equality
          y + x - y
        ≈⟨ +ᴹ-cong (+ᴹ-comm y x) refl ⟩
          x + y - y
        ≈⟨ +ᴹ-assoc x y (- y) ⟩
          x + (y - y)
        ≈⟨ +ᴹ-cong {x = x} refl (-ᴹ‿inverseʳ y) ⟩
          x + 0.0
        ≈⟨ +ᴹ-identityʳ x ⟩
          x
        ∎

  times : Float → Float → Float
  times = _*_

  times-homo : ∀ m → IsModuleHomomorphism +-*-module +-*-module (times m)
  times-homo = todo

  _SlopeOf_At_ : (f' : MA.X → MB.X) (f : MA.X → MB.X) (x : MA.X) → Set _
  f' SlopeOf f At x = (λ y dy → f' y * dy) Differentiates f At x

  dxⁿ≈nxⁿ⁻¹
    : ∀ x n → (1.0 < n) ⊎ (¬ x ≈ 0.0)
    → (λ y → (n * (y ** (n - 1.0)))) SlopeOf (_** n) At x
  dxⁿ≈nxⁿ⁻¹ = todo

  dlogx≈1÷x : ∀ x → ¬ x ≈ 0.0 → (λ y dy → dy ÷ y) Differentiates log At x
  dlogx≈1÷x = todo

  deˣ/dx≈eˣ : ∀ x → e^_ SlopeOf e^_ At x
  deˣ/dx≈eˣ = todo

  open import Function using (_∘_)

  -- chain'
  --   : ∀ f f' g g' x
  --   → (λ dx → dx * f' x) Differentiates f At x
  --   → (λ dx → dx * g' (f x)) Differentiates g At f x
  --   → (λ dx → g'fx * (f'x dx)) Differentiates (g ∘ f) At x
  -- chain' f g x (f'x , _) (g'fx , _) = (λ dx → g'fx (f'x dx)) , todo

  ∂exp : ∀ x → (λ y dy → dy * (e^ y)) Differentiates e^_ At x
  ∂exp x = todo


  open import Data.Nat using (zero; suc)
  instance
    exp-n-∂ : ∀ {n} {x} → e^_ ⟦ x , n ⟧
    exp-n-∂ {zero} = []
    exp-n-∂ {n = suc n} = todo ∹ exp-n-∂


  it : ∀ {a} {A : Set a} → {{A}} → A
  it {{x}} = x

  gradexp : ∀ {x} → e^_ ⟦ x , 0 ⟧
  gradexp = it


  chain
    : ∀ f g x {n}
    → ⦃ f ⟦ x , n ⟧ ⦄
    → ⦃ g ⟦ f x , n ⟧ ⦄
    → (g ∘ f) ⟦ x , n ⟧
  chain f g x {n = 0} = []
  chain f g x {_} ⦃ _∹_ {_} {f'} pf ff ⦄ ⦃ _∹_ {_} {g'} pg gg ⦄ =
    let h y dy = g' (f y) (f' y dy)
    -- confusion here between xs and dxs.
    in _∹_ {δf = h} todo (chain (f' x) (g' (f x)) x ⦃ ff ⦄ ⦃ {! gg  !} ⦄)

  exp : Float → Float
  exp = e^_

  asdf : ∀ x → (exp ∘ exp) ⟦ x , 1 ⟧
  asdf x = chain exp exp x


--   gradsin : ∀ {x} → sin DifferentiableAt x
--   gradsin {x} = (λ dx → dx * (cos x)) , todo

--   gradcos : ∀ {x} → cos DifferentiableAt x
--   gradcos {x} = (λ dx → dx * (- sin x)) , todo

--   grad : ∀ f x → f DifferentiableAt x → Float → Float
--   grad f x (f'x , _) = f'x


--   teste : Float → Float
--   teste x = grad e^_ x (grade^ {x}) 1.0

--   -- testsin : Float → Float
--   -- testsin x = grad sin x (gradsin x) 1.0

--   -- test : Float → Float
--   -- test x = grad (e^_ ∘ sin) x (chain' sin e^_ x (gradsin x) (grade^ (sin x))) 1.0
  
--   -- _ : ∀ x → test x ≡ 1.0 * cos x * (e^ sin x)
--   -- _ = λ x → refl


--   -- -- TODO
--   -- -- definitely need some helper functions here.
--   -- _ : ∀ y n → (λ x → n * y ** (n - 1.0) * x) Differentiates (λ x → x ** n) At y
--   -- _ = λ y n → todo , λ ε 0<ε → δ₀ ε y n , λ δ (0<δ , δ<ε) → proof y n ε δ 0<δ δ<ε
--   --   where
--   --     δ₀ : Float → Float → Float → Float
--   --     δ₀ = {!   !}

--   --     triangle : ∀ x y → ∥ x + y ∥ < ∥ x ∥ + ∥ y ∥
--   --     triangle = todo

--   --     ≈< : ∀ x {y z} → y < z → x + y < x + z
--   --     ≈< = todo

--   --     -- does this imply _≈_ is _≡_?
--   --     ∀-cong : ∀ {x y} (f : CR.X → CR.X) → x ≈ y → f x ≈ f y
--   --     ∀-cong = todo

--   --     proof
--   --       : ∀ y n ε Δ (0<Δ : 0.0 < ∥ Δ ∥) (Δ<ε : ∥ Δ ∥ < ε)
--   --       → ∥ (y + Δ) ** n - (y ** n +ᴹ n * y ** (n - 1.0) * Δ) ∥ < ε
--   --     proof y n ε Δ 0<Δ Δ<ε =
--   --       begin-strict
--   --         ∥ (y + Δ) ** n - (y ** n + n * y ** (n - 1.0) * Δ) ∥
--   --       <⟨ triangle ((y + Δ) ** n) _ ⟩
--   --         ∥ (y + Δ) ** n ∥ + ∥ - (y ** n + n * y ** (n - 1.0) * Δ) ∥
--   --       ≈⟨ +-cong { ∥ (y + Δ) ** n ∥ } refl (sqrt-cong (∥-x∥²≈∥x∥² ((y ** n + n * y ** (n - 1.0) * Δ)))) ⟩
--   --         ∥ (y + Δ) ** n ∥ + ∥ (y ** n + n * y ** (n - 1.0) * Δ) ∥
--   --       <⟨ ≈< ∥ (y + Δ) ** n ∥ (triangle (y ** n) _) ⟩
--   --         ∥ (y + Δ) ** n ∥ + (∥ y ** n ∥ + ∥ n * y ** (n - 1.0) * Δ ∥)
--   --       <⟨ {! +-cong refl (x→-x _) !} ⟩
--   --         ε
--   --       ∎



-- --   -- (f (x MA.+ᴹ dx) MB.+ᴹ (MB.-ᴹ (f x MB.+ᴹ f' dx))) ⟶ MB.0ᴹ as dx ⟶ MA.0ᴹ
-- --   _ : ∀ θ → (λ dθ → F.cos θ F.* dθ) Differentiates F.sin At θ
-- --   _ =
-- --     λ θ → times-homo (F.cos θ) ,
-- --       λ ε → ε ,
-- --         λ dθ (0<abs[dθ-0] , abs[dθ-0]<ε) → {!   !} -- abs[x-0]<ε→abs[c+x-c]<ε x ε {! F.sin (θ F.+ x) !} abs[x-0]<ε
-- --         -- if abs dθ < ε then abs ( sin (θ + dθ) - (sin θ + cos θ * dθ) ) < ε

-- --         -- sin x = (e^iπx - e^-iπx) / 2i
-- --         -- cos x = (e^iπx + e^-iπx) / 2
-- --         -- sin x+dx = ?


-- -- --   open Diff +-*-module +-*-module
-- -- --   open Line +-*-commutativeRing

-- -- --   dline : ∀ m b x → Differentiable _≤_ abs abs (line m b) x
-- -- --   dline m b x = (λ x' dx → m * dx) , {!   !} , λ dy → (dy F.÷ m) , {! asdf dy  !}
-- -- --     where
-- -- --       open import Relation.Binary.Reasoning.PartialOrder ≤-poset

-- -- --       diff≈0 : ∀ dx → (line m b (x + dx) - line m b x) - m * dx ≈ 0#
-- -- --       diff≈0 dx =
-- -- --         begin-equality
-- -- --           (line m b (x + dx) - line m b x - m * dx)
-- -- --         ≈⟨ +-cong (linear-diff m b x dx) refl ⟩
-- -- --           m * dx - m * dx
-- -- --         ≈⟨ proj₂ -‿inverse (m * dx) ⟩
-- -- --           0#
-- -- --         ∎

-- -- --   open import Data.Nat using (ℕ; zero; suc)


 
-- -- -- --
-- -- -- --   Convex : (A → A) → Set


-- -- -- -- minimize : (f : A → A) (c : Convex f) → A
-- -- -- -- minimize f c = {!   !}


-- -- -- -- gradient : (f : A → A) (Differentiable f)

-- -- -- -- gradientDescent : (f' : A → A) (n : ℕ) → A
-- -- -- -- gradientDescent = ? 

-- --   -- open import Relation.Nullary using (¬_)

-- --   -- x<y→y≮x : ∀ {x y} → x < y → ¬ y < x
-- --   -- x<y→y≮x x y = post


-- --   -- <-trans : ∀ {i j k} → i < j → j < k → i < k
-- --   -- <-trans i<j j<k = post


-- --   -- open CommutativeRing +-*-commutativeRing
-- --   -- open Module +-*-module
-- --   -- open import Relation.Binary

-- --   -- ≤-antisym : Antisymmetric _≡_ _≤_
-- --   -- ≤-antisym (inj₂ i≡j) j≤i = i≡j
-- --   -- ≤-antisym (inj₁ i<j) (inj₂ j≡i) = sym j≡i
-- --   -- ≤-antisym {i} {j} (inj₁ i<j) (inj₁ j<i) with x<y→y≮x {i} {j} i<j j<i
-- --   -- ... | ()

-- --   -- ≤-trans : Transitive _≤_
-- --   -- ≤-trans {i} {j} {k} (inj₁ i<j) (inj₁ j<k) = inj₁ (<-trans {i} {j} {k} i<j j<k)
-- --   -- ≤-trans (inj₁ i<j) (inj₂ j≡k) = inj₁ {! tt  !}
-- --   -- ≤-trans (inj₂ y) (inj₁ x) = {!   !}
-- --   -- ≤-trans (inj₂ i≡j) (inj₂ j≡k) = inj₂ (trans i≡j j≡k)
