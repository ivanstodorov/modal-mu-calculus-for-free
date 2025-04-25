{-# OPTIONS --without-K --sized-types --guardedness #-}
module ModalLogics.WithoutContainerization.Test where

open import Agda.Builtin.Size using (Size; Size<_)
open import Data.Container using (Container; ⟦_⟧)
open import Data.Product using (_,_)
open import Level using (Level; _⊔_)

private variable
  a s p r r₁ r₂ : Level

mutual
  data Free {i : Size} (C : Container s p) (R : Set r) : Set (s ⊔ p ⊔ r) where
    pure   : R                      → Free {i = i} C R
    impure : ⟦ C ⟧ (CoFree {i = i} C R) → Free {i = i} C R

  record CoFree {i : Size} (C : Container s p) (R : Set r) : Set (s ⊔ p ⊔ r) where
    coinductive
    constructor ⦗_⦘
    field
      free : ∀{j : Size< i} → Free {i = j} C R

open CoFree public

_>>=_ : {i : Size} → {C : Container s p} → {R₁ : Set r₁} → {R₂ : Set r₂} → CoFree {i = i} C R₁ → (R₁ → CoFree {i = i} C R₂) → CoFree {i = i} C R₂
free (a >>= b) with free a
... | pure x = free (b x)
... | impure (s , c) = impure (s , λ p → c p >>= b)

_>>_ : {i : Size} → {C : Container s p} → {R₁ : Set r₁} → {R₂ : Set r₂} → CoFree {i = i} C R₁ → CoFree {i = i} C R₂ → CoFree {i = i} C R₂
a >> b = a >>= λ _ → b

Program : Container s p → Set r → Set (s ⊔ p ⊔ r)
Program = CoFree
