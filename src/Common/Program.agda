{-# OPTIONS --without-K --safe #-}
module Common.Program where

open import Data.Container using (Container)
open import Data.Container.FreeMonad using (_⋆_)
open import Level using (Level; _⊔_)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

Program : Container ℓ₁ ℓ₂ → (I : Set ℓ₃) → (I → Set ℓ₄) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Program C I O = (i : I) → C ⋆ O i
