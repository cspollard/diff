open import Relation.Binary using (Rel)
open import Algebra.Bundles using (CommutativeRing)

open import Algebra.Module.Normed

module Algebra.Module.Limit.Compose
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  {ma ℓma} (MA : NormedModule CR _≤_ ma ℓma)
  {mb ℓmb} (MB : NormedModule CR _≤_ mb ℓmb)
  {mc ℓmc} (MC : NormedModule CR _≤_ mc ℓmc)
  where

open import Data.Product using (_,_)
open import Function using (_∘_)

open CommutativeRing CR
open import Assume using (assume)

import Algebra.Module.Limit as Limit

open Limit MA MB using () renaming
  ( _DifferentiableAt_ to _DifferentiableAt₁₂_
  ; Differentiable to Differentiable₁₂
  )

open Limit MB MC using () renaming
  (_DifferentiableAt_ to _DifferentiableAt₂₃_
  ; Differentiable to Differentiable₂₃
  )

open Limit MA MC using () renaming
  (_DifferentiableAt_ to _DifferentiableAt₁₃_
  ; Differentiable to Differentiable₁₃
  )

private
  module MA = NormedModule MA
  module MB = NormedModule MB
  module MC = NormedModule MC

∘-differentiable-at : ∀ {g f x} → g DifferentiableAt₂₃ (f x) → f DifferentiableAt₁₂ x → (g ∘ f) DifferentiableAt₁₃ x
∘-differentiable-at {g} {f} {x} (Dg , _) (Df , _) = (Dg ∘ Df) , assume

∘-differentiable : ∀ {g f} → Differentiable₂₃ g → Differentiable₁₂ f → Differentiable₁₃ (g ∘ f)
∘-differentiable {g} {f} diff-g diff-f = λ x → ∘-differentiable-at {g} {f} {x} (diff-g (f x)) (diff-f x)
