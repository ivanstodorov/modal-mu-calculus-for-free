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
  ℓ ℓₛ ℓₚ ℓₓ ℓ₁ : Level
  S : Set ℓ
  C : Container ℓₛ ℓₚ
  X : Set ℓₓ
  αs : List (Set ℓ₁ ⊎ Set ℓ₁)

postulate
  ∈-dec : (s : S) → (af : ActionFormula S ℓ₁) → Dec (s ∈ af)
  ⊨-dec : (x : Program C X) → (f : Formula (Shape C) ℓ₁ αs) → Dec (x ⊨ f)
