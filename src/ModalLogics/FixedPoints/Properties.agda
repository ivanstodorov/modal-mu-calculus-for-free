{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.FixedPoints.Properties where

open import Common.Program using (Program)
open import Common.RegularFormulas using (ActionFormula; _∈_)
open import Data.Container using (Container; Shape)
open import Level using (Level)
open import ModalLogics.FixedPoints.Base using (Formula; _⊨_)
open import Relation.Nullary using (Dec)

private variable
  ℓ₁ ℓ₂ ℓ₃ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ∈-dec : (s : Shape C) → (af : ActionFormula C) → Dec (s ∈ af)
  ⊨-dec : (x : Program C α) → (f : Formula C) → Dec (x ⊨ f)
