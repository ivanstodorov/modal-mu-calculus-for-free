{-# OPTIONS --without-K --safe #-}
module Common.RegularFormulas where

open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Container using (Container; Shape)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary.Decidable using (⌊_⌋)

open Bool
open IsDecEquivalence ⦃...⦄

private variable
  ℓ₁ ℓ₂ : Level

infix 100 act_
infix 95 ¬_
infixr 90 _∩_
infixr 85 _∪_

data ActionFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : ActionFormula C
  act_ : Shape C → ActionFormula C
  ¬_ : ActionFormula C → ActionFormula C
  _∩_ _∪_ : ActionFormula C → ActionFormula C → ActionFormula C

infix 25 _⊩ᵃᶠ_

_⊩ᵃᶠ_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → ActionFormula C → Shape C → Bool
true ⊩ᵃᶠ _ = true
false ⊩ᵃᶠ _ = false
act s₁ ⊩ᵃᶠ s₂ = ⌊ s₁ ≟ s₂ ⌋
¬ af ⊩ᵃᶠ s = not (af ⊩ᵃᶠ s)
af₁ ∪ af₂ ⊩ᵃᶠ s = af₁ ⊩ᵃᶠ s ∨ af₂ ⊩ᵃᶠ s
af₁ ∩ af₂ ⊩ᵃᶠ s = af₁ ⊩ᵃᶠ s ∧ af₂ ⊩ᵃᶠ s

infix 80 actF_
infix 75 _*
infix 75 _⁺
infixr 70 _·_
infixr 65 _+_

data RegularFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  ε : RegularFormula C
  actF_ : ActionFormula C → RegularFormula C
  _·_ _+_ : RegularFormula C → RegularFormula C → RegularFormula C
  _* _⁺ : RegularFormula C → RegularFormula C

data RegularFormula⁺ (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  ε : RegularFormula⁺ C
  actF_ : ActionFormula C → RegularFormula⁺ C
  _·_ _+_ : RegularFormula⁺ C → RegularFormula⁺ C → RegularFormula⁺ C
  _* : RegularFormula⁺ C → RegularFormula⁺ C

rf→rf⁺ : {C : Container ℓ₁ ℓ₂} → RegularFormula C → RegularFormula⁺ C
rf→rf⁺ ε = ε
rf→rf⁺ (actF af) = actF af
rf→rf⁺ (rf₁ · rf₂) = rf→rf⁺ rf₁ · rf→rf⁺ rf₂
rf→rf⁺ (rf₁ + rf₂) = rf→rf⁺ rf₁ + rf→rf⁺ rf₂
rf→rf⁺ (rf *) = rf→rf⁺ rf *
rf→rf⁺ (rf ⁺) = rf⁺ · (rf⁺ *)
  where
  rf⁺ = rf→rf⁺ rf
