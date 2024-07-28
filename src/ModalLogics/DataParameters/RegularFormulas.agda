{-# OPTIONS --without-K --safe #-}
module ModalLogics.DataParameters.RegularFormulas where

open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; suc; _⊔_; Lift)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

private variable
  ℓ ℓ₁ : Level

infix 125 val_
infix 125 act_
infix 120 _ᶜ
infixr 115 _∩_
infixr 110 _∪_
infix 105 ∀〔_〕_
infix 105 ∃〔_〕_

data ActionFormula (S : Set ℓ) (ℓ₁ : Level) : Set (ℓ ⊔ (suc ℓ₁)) where
  true false : ActionFormula S ℓ₁
  val_ : Set ℓ₁ → ActionFormula S ℓ₁
  act_ : S → ActionFormula S ℓ₁
  _ᶜ : ActionFormula S ℓ₁ → ActionFormula S ℓ₁
  _∩_ _∪_ : ActionFormula S ℓ₁ → ActionFormula S ℓ₁ → ActionFormula S ℓ₁
  ∀〔_〕_ ∃〔_〕_ : (α : Set ℓ₁) → (α → ActionFormula S ℓ₁) → ActionFormula S ℓ₁

infix 25 _∈_

_∈_ : {S : Set ℓ} → S → ActionFormula S ℓ₁ → Set (ℓ ⊔ ℓ₁)
_ ∈ true = ⊤
_ ∈ false = ⊥
_∈_ {ℓ = ℓ} {ℓ₁ = ℓ₁} _ (val x) = Lift (ℓ ⊔ ℓ₁) x
_∈_ {ℓ = ℓ} {ℓ₁ = ℓ₁} s₁ (act s₂) = Lift (ℓ ⊔ ℓ₁) (s₁ ≡ s₂)
s ∈ af ᶜ = ¬ s ∈ af
s ∈ af₁ ∩ af₂ = s ∈ af₁ × s ∈ af₂
s ∈ af₁ ∪ af₂ = s ∈ af₁ ⊎ s ∈ af₂
s ∈ ∀〔 _ 〕 af = ∀ a → s ∈ af a
s ∈ ∃〔 _ 〕 af = ∃[ a ] s ∈ af a

infix 100 actF_
infix 95 _*
infix 95 _⁺
infixr 90 _·_
infixr 85 _+_

data RegularFormula (S : Set ℓ) (ℓ₁ : Level) : Set (ℓ ⊔ (suc ℓ₁)) where
  ε : RegularFormula S ℓ₁
  actF_ : ActionFormula S ℓ₁ → RegularFormula S ℓ₁
  _·_ _+_ : RegularFormula S ℓ₁ → RegularFormula S ℓ₁ → RegularFormula S ℓ₁
  _* _⁺ : RegularFormula S ℓ₁ → RegularFormula S ℓ₁
