module Common.Free where

open import Common.Effect

data Free (ε : Effect) (α : Set) : Set where
  pure : α → Free ε α
  step : (c : Effect.C ε) → (Effect.R ε c → Free ε α) → Free ε α

open Free

map : {ε : Effect} → {α β : Set} →
  (α → β) → Free ε α → Free ε β
map f (pure a) = pure (f a)
map f (step c k) = step c (λ r → map f (k r))

return : {ε : Effect} → {α : Set} →
  α → Free ε α
return = pure

_>>=_ : {ε : Effect} → {α β : Set} →
  Free ε α → (α → Free ε β) → Free ε β
pure a >>= f = f a
step c k >>= f = step c (λ r → k r >>= f)
