open import Relation.Binary using (Rel)
open import Algebra.Bundles using (CommutativeRing)

open import Normed

module Beside
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  {ma ℓma} (MA : NormedModule CR _≤_ ma ℓma)
  {mb ℓmb} (MB : NormedModule CR _≤_ mb ℓmb)
  {mc ℓmc} (MC : NormedModule CR _≤_ mc ℓmc)
  {md ℓmd} (MD : NormedModule CR _≤_ md ℓmd)
  where

open import Data.Product using (_,_; map)
open import Function using (_∘_)

open CommutativeRing CR
open import Limit using (D[_,_][_,_])
open import Assume using (assume)

private
  MAC = directProduct MA MC
  MBD = directProduct MB MD

  module MA = NormedModule MA
  module MB = NormedModule MB
  module MC = NormedModule MC
  module MD = NormedModule MD
  module MAC = NormedModule MAC
  module MBD = NormedModule MBD

⊗-differentiable-at : ∀ {f g x y} → D[ MA , MB ][ f , x ] → D[ MC , MD ][ g , y ] → D[ MAC , MBD ][ map f g , (x , y) ]
⊗-differentiable-at (f' , _) (g' , _) = (λ (x , y) (dx , dy) → f' x dx , g' y dy) , assume
