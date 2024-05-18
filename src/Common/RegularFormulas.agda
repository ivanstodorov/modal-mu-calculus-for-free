{-# OPTIONS --without-K --safe #-}
module Common.RegularFormulas where

open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

private variable
  ℓ₁ ℓ₂ : Level

infix 100 act_
infix 95 _ᶜ
infixr 90 _∩_
infixr 85 _∪_

data ActionFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : ActionFormula C
  act_ : Shape C → ActionFormula C
  _ᶜ : ActionFormula C → ActionFormula C
  _∩_ _∪_ : ActionFormula C → ActionFormula C → ActionFormula C

infix 25 _∈_

_∈_ : {C : Container ℓ₁ ℓ₂} → Shape C → ActionFormula C → Set ℓ₁
_ ∈ true = ⊤
_ ∈ false = ⊥
s₁ ∈ act s₂ = s₁ ≡ s₂
s ∈ af ᶜ = ¬ s ∈ af
s ∈ af₁ ∩ af₂ = s ∈ af₁ × s ∈ af₂
s ∈ af₁ ∪ af₂ = s ∈ af₁ ⊎ s ∈ af₂

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
