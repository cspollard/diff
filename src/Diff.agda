module Diff where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float
open import Function using (_∘_)

postulate
  post : ∀ {a} {A : Set a} → A


-- Need to generalize for bilinear forms
data _Is_DiffAt_ (f : Float → Float) : ℕ → Float → Set where
  continuous : ∀ x → f Is zero DiffAt x
  d : ∀ f' {n} x → f' Is n DiffAt x → f Is suc n DiffAt x


data D (A : Set) : ℕ → A → Set where




-- +-diff : ∀ {x} {n} → HasDeriv (x +_) n
-- +-diff {x} {zero} = d⁰
-- +-diff {x} {suc n} = d (x +_) (+-diff {x} {n})


instance
  chain : ∀ {f g n x} → ⦃ f Is n DiffAt x ⦄ → ⦃ g Is n DiffAt g x ⦄ → (f ∘ g) Is n DiffAt x
  chain = post

  -‿diff : ∀ {n x} → -_ Is n DiffAt x
  -‿diff {zero} {x} = continuous x
  -‿diff {suc n} {x} = d -_ x -‿diff

  exp-diff : ∀ {n x} → e^_ Is n DiffAt x
  exp-diff {zero} {x} = continuous x
  exp-diff {suc n} {x} = d e^_ x exp-diff

  mutual
    sin-diff : ∀ {n x} → sin Is n DiffAt x
    sin-diff {zero} {x} = continuous x
    sin-diff {suc n} {x} = d cos x cos-diff

    cos-diff : ∀ {n x} → cos Is n DiffAt x
    cos-diff {zero} {x} = continuous x
    cos-diff {suc n} {x} = d (-_ ∘ sin) x (chain { -_} {sin}) -- (chain -_ sin)


∂ : ∀ f x → ⦃ f Is 1 DiffAt x ⦄ → Float
∂ f x ⦃ d f' x _ ⦄ = f' x

syntax ∂ (λ x → fx) y = ∂ fx /∂ x at y

test : Float → Float
test y = ∂ (cos (e^ x)) /∂ x at y


-- -- run : (∀ {n} → F₁) → F₁
-- -- run f x = f {zero} x
