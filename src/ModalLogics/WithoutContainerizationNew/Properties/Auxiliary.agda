{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.Auxiliary where

open import Level using (Level)

private variable
  ℓ : Level

record Inhabited (α : Set ℓ) : Set ℓ where
  constructor defaultᶜ
  field
    default : α
