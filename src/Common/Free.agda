module Common.Free where

open import Common.Effect
open import Level using (Level; _⊔_)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Free (ε : Effect {ℓ₁} {ℓ₂}) (α : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  pure : α → Free ε α
  step : (c : Effect.C ε) → (Effect.R ε c → Free ε α) → Free ε α

open Free

map : {ε : Effect {ℓ₁} {ℓ₂}} → {α : Set ℓ₃} {β : Set ℓ₄} → (α → β) → Free ε α → Free ε β
map f (pure a) = pure (f a)
map f (step c k) = step c (λ r → map f (k r))

return : {ε : Effect {ℓ₁} {ℓ₂}} → {α : Set ℓ₃} → α → Free ε α
return = pure

_>>=_ : {ε : Effect {ℓ₁} {ℓ₂}} → {α : Set ℓ₃} {β : Set ℓ₄} → Free ε α → (α → Free ε β) → Free ε β
pure a >>= f = f a
step c k >>= f = step c (λ r → k r >>= f)
