{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.DataParameters.Properties where

open import Common.Program using (Program)
open import Data.Container using (Container; Shape)
open import Data.List using (List)
open import Data.Sum using (_⊎_)
open import Level using (Level)
open import ModalLogics.DataParameters.Base using (Formula; _⊨_)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; _∈_)
open import Relation.Nullary using (Dec)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃
  αs : List (Set ℓ ⊎ Set ℓ)

postulate
  ∈-dec : (s : Shape C) → (af : ActionFormula C ℓ) → Dec (s ∈ af)
  ⊨-dec : (x : Program C α) → (f : Formula C ℓ αs) → Dec (x ⊨ f)
