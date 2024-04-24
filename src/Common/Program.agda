{-# OPTIONS --without-K --safe --guardedness #-}
module Common.Program where

open import Data.Container using (Container; ⟦_⟧)
open import Data.Product using (_,_)
open import Level using (Level; _⊔_)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Free (F : Container ℓ₁ ℓ₂ → Set ℓ₃ → Set ℓ₄) (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  pure : α → Free F C α
  impure : ⟦ C ⟧ (F C α) → Free F C α

module Inductive where

  record IndFree (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    inductive
    constructor ⦗_⦘
    field
      free : Free IndFree C α

  _>>=_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {β : Set ℓ₄} → IndFree C α → (α → IndFree C β) → IndFree C β
  ⦗ pure x ⦘ >>= b = b x
  ⦗ impure (s , c) ⦘ >>= b = ⦗ impure (s , (λ p → c p >>= b)) ⦘

  _>>_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {β : Set ℓ₄} → IndFree C α → IndFree C β → IndFree C β
  a >> b = a >>= λ _ → b

module Coinductive where

  record CoFree (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    coinductive
    constructor ⦗_⦘
    field
      free : Free CoFree C α

  open CoFree

  _>>=_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {β : Set ℓ₄} → CoFree C α → (α → CoFree C β) → CoFree C β
  free (a >>= b) with free a
  ... | pure x = free (b x)
  ... | impure (s , c) = impure (s , λ p → c p >>= b)

  _>>_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {β : Set ℓ₄} → CoFree C α → CoFree C β → CoFree C β
  a >> b = a >>= λ _ → b

open Coinductive using (CoFree)
open Coinductive using (⦗_⦘; _>>=_; _>>_) public

open CoFree public

Program : Container ℓ₁ ℓ₂ → Set ℓ₃ → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
Program = CoFree

ParameterizedProgram : Container ℓ₁ ℓ₂ → (I : Set ℓ₃) → (I → Set ℓ₄) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
ParameterizedProgram C I O = (i : I) → Program C (O i)
