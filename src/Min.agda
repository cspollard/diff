module Min where

open import Data.Nat using (ℕ; zero; suc)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Bundles using (Module)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Core using (Rel)
import Algebra.Module.Construct.Zero as Zero
import Algebra.Module.Construct.DirectProduct as Prod
import Algebra.Module.Construct.TensorUnit as Unit


module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  {ma ℓma} (MA : Module CR ma ℓma)
  {mb ℓmb} (MB : Module CR mb ℓmb)
  where

  open import Linear MA MB

  module _
    {rel} (_<_ : Rel (CommutativeRing.Carrier CR) rel)
    (∥_∥ᴬ : A → R)
    (∥_∥ᴮ : B → R)
    (_÷_ : B → R → B)
    where


    _LimitOf_x→_ Limit-syntax : (L : B) (f : A → B) (c : A)→ Set _
    L LimitOf f x→ c = ∀ ε → ∃[ δ ] ∥ (f (c +ᴬ δ) -ᴮ L) ∥ᴮ < ∥ ε ∥ᴮ
    Limit-syntax = _LimitOf_x→_


    syntax Limit-syntax L (λ h → f) c = L LimitOf f ∶ h ⟶ c


    Diff' : (f : A → B) (x : A) (f' : A → A → B) → Set _
    Diff' f x f' = 0ᴮ LimitOf tmp dx ∶ dx ⟶ 0ᴬ
      where
        tmp : (dx : A) → B
        tmp dx = (f (x +ᴬ dx) -ᴮ f x -ᴮ f' x dx) ÷ ∥ dx ∥ᴬ


    Differentiable : (f : A → B) → A → Set _
    Differentiable f x =
      Σ[ f' ∈ (A → A → B) ]
          Linear (f' x)
        -- × ∀ dy → ∃[ dx ] (∥ ((f (x +ᴬ dx) -ᴮ f x) -ᴮ (f' x dx)) ∥ᴮ) < (∥ dy ∥ᴮ)
        
    D : {f : A → B} {x : A} (d : Differentiable f x) → A → B
    D {x = x} d = proj₁ d x


n-module : ∀ {a b} {S : CommutativeRing a b} → ℕ → Module S a b
n-module zero = Zero.⟨module⟩
n-module (suc n) = Prod.⟨module⟩ Unit.⟨module⟩ (n-module n)

open import Tactic.RingSolver

module Line {a b} (CR : CommutativeRing a b) where
  open CommutativeRing CR
  open import Relation.Binary.Reasoning.Setoid setoid

  open import Tactic.RingSolver.Core.AlmostCommutativeRing

  line : Carrier → Carrier → Carrier → Carrier
  line m b x = m * x + b

  x+y-x≈y : ∀ x y → (x + y) - x ≈ y
  x+y-x≈y x y =
    begin
      (x + y) - x
    ≈⟨ +-assoc x y (- x) ⟩
      x + (y - x)
    ≈⟨ +-cong refl (+-comm y (- x)) ⟩
      x + (- x + y)
    ≈⟨ sym (+-assoc x (- x) y) ⟩
      (x - x) + y
    ≈⟨ +-cong (proj₂ -‿inverse x) refl ⟩
      0# + y
    ≈⟨ +-identityˡ y ⟩
      y
    ∎

  x+y+z≈x+z+y : ∀ x y z → x + y + z ≈ x + z + y
  x+y+z≈x+z+y x y z =
    begin
      (x + y) + z
    ≈⟨ +-assoc x y z ⟩
      x + (y + z)
    ≈⟨ +-cong refl (+-comm y z) ⟩
      x + (z + y)
    ≈⟨ sym (+-assoc x z y) ⟩
      (x + z) + y
    ∎

  linear-diff : ∀ m b x dy → line m b (x + dy) - line m b x ≈ m * dy
  linear-diff m b x dy =
    begin
      m * (x + dy) + b - (m * x + b)
    ≈⟨ +-cong (+-cong (distribˡ m x dy) refl) refl ⟩
      m * x + m * dy + b - (m * x + b)
    ≈⟨ +-cong (x+y+z≈x+z+y (m * x) (m * dy) b) refl ⟩
      m * x + b + m * dy - (m * x + b)
    ≈⟨ x+y-x≈y (m * x + b) (m * dy) ⟩
      m * dy
    ∎

