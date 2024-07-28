{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.RegularFormulas.Properties where

open import Common.Program using (Program)
open import Common.RegularFormulas using (ActionFormula; _∈_)
open import Data.Container using (Container; Shape)
open import Level using (Level)
open import ModalLogics.RegularFormulas.Base using (Formula; _⊨_)
open import Relation.Nullary using (Dec)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  S : Set ℓ
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ∈-dec : (s : S) → (af : ActionFormula S) → Dec (s ∈ af)
  ⊨-dec : (x : Program C α) → (f : Formula (Shape C)) → Dec (x ⊨ f)
