{-# OPTIONS --without-K --safe #-}
module Common.ActionFormulas where

open import Data.Bool using (Bool; _∧_; _∨_) renaming (not to notᵇ)
open import Data.Container using (Container; Shape)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary.Decidable using (⌊_⌋)

open Bool
open IsDecEquivalence ⦃...⦄

private variable
  ℓ₁ ℓ₂ : Level

infix 60 act
infix 60 not
infixr 55 _∪_
infixr 55 _∩_

data ActionFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  all none : ActionFormula C
  act : Shape C → ActionFormula C
  not : ActionFormula C → ActionFormula C
  _∪_ _∩_ : ActionFormula C → ActionFormula C → ActionFormula C

parseActF : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → ActionFormula C → Shape C → Bool
parseActF all _ = true
parseActF none _ = false
parseActF (act s₁) s₂ = ⌊ s₁ ≟ s₂ ⌋
parseActF (not af) s = notᵇ (parseActF af s)
parseActF (af₁ ∪ af₂) s = parseActF af₁ s ∨ parseActF af₂ s
parseActF (af₁ ∩ af₂) s = parseActF af₁ s ∧ parseActF af₂ s
