module Common.Free where

open import Common.Effect

-- data Free (C : Set) (R : C → Set) (a : Set) : Set where
--   Pure : a → Free C R a
--   Step : (c : C) → (R c → Free C R a) → Free C R a

data Free (e : Effect) (a : Set) : Set where
  Pure : a → Free e a
  Step : (c : Effect.C e) → (Effect.R e c → Free e a) → Free e a

open Free

-- map : {C : Set} → {R : C → Set} → {a b : Set} →
--   (a → b) → Free C R a → Free C R b
-- map f (Pure x) = Pure (f x)
-- map f (Step c k) = Step c (λ r → map f (k r))

map : {e : Effect} → {a b : Set} →
  (a → b) → Free e a → Free e b
map f (Pure x) = Pure (f x)
map f (Step c k) = Step c (λ r → map f (k r))

-- return : {C : Set} → {R : C → Set} → {a : Set} →
--   a → Free C R a
-- return = Pure

return : {e : Effect} → {a : Set} →
  a → Free e a
return = Pure

-- _>>=_ : {C : Set} → {R : C → Set} → {a b : Set} →
--   Free C R a → (a → Free C R b) → Free C R b
-- Pure x >>= f = f x
-- Step c x >>= f = Step c (λ r → x r >>= f)

_>>=_ : {e : Effect} → {a b : Set} →
  Free e a → (a → Free e b) → Free e b
Pure x >>= f = f x
Step c x >>= f = Step c (λ r → x r >>= f)
