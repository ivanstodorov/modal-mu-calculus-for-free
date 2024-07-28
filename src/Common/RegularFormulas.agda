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
  ℓ : Level

infix 100 act_
infix 95 _ᶜ
infixr 90 _∩_
infixr 85 _∪_

data ActionFormula (S : Set ℓ) : Set ℓ where
  true false : ActionFormula S
  act_ : S → ActionFormula S
  _ᶜ : ActionFormula S → ActionFormula S
  _∩_ _∪_ : ActionFormula S → ActionFormula S → ActionFormula S

infix 25 _∈_

_∈_ : {S : Set ℓ} → S → ActionFormula S → Set ℓ
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

data RegularFormula (S : Set ℓ) : Set ℓ where
  ε : RegularFormula S
  actF_ : ActionFormula S → RegularFormula S
  _·_ _+_ : RegularFormula S → RegularFormula S → RegularFormula S
  _* _⁺ : RegularFormula S → RegularFormula S
