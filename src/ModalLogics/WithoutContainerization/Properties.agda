{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.WithoutContainerization.Properties where

open import Common.Program using (Program)
open import Common.RegularFormulasWithData using (ActionFormula; _∈_)
open import Data.Container using (Container; Shape)
open import Level using (Level)
open import ModalLogics.WithoutContainerization.Base using (Formula; _⊨_)
open import Relation.Nullary using (Dec)

private variable
  s ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  S : Set s
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ∈-dec : (s : S) → (af : ActionFormula S ℓ) → Dec (s ∈ af)
  ⊨-dec : (x : Program C α) → (f : Formula (Shape C) ℓ) → Dec (x ⊨ f)
