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
  ℓ ℓ₁ ℓ₂ : Level

infix 125 val_
infix 125 act_
infix 120 _ᶜ
infixr 115 _∩_
infixr 110 _∪_
infix 105 ∀〔_〕_
infix 105 ∃〔_〕_

data ActionFormula (C : Container ℓ₁ ℓ₂) (ℓ : Level) : Set ((suc ℓ) ⊔ ℓ₁) where
  true false : ActionFormula C ℓ
  val_ : Set ℓ → ActionFormula C ℓ
  act_ : Shape C → ActionFormula C ℓ
  _ᶜ : ActionFormula C ℓ → ActionFormula C ℓ
  _∩_ _∪_ : ActionFormula C ℓ → ActionFormula C ℓ → ActionFormula C ℓ
  ∀〔_〕_ ∃〔_〕_ : (α : Set ℓ) → (α → ActionFormula C ℓ) → ActionFormula C ℓ

infix 25 _∈_

_∈_ : {C : Container ℓ₁ ℓ₂} → Shape C → ActionFormula C ℓ → Set (ℓ ⊔ ℓ₁)
_ ∈ true = ⊤
_ ∈ false = ⊥
_∈_ {ℓ₁ = ℓ₁} {ℓ = ℓ} _ (val x) = Lift (ℓ ⊔ ℓ₁) x
_∈_ {ℓ₁ = ℓ₁} {ℓ = ℓ} s₁ (act s₂) = Lift (ℓ ⊔ ℓ₁) (s₁ ≡ s₂)
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

data RegularFormula (C : Container ℓ₁ ℓ₂) (ℓ : Level) : Set ((suc ℓ) ⊔ ℓ₁) where
  ε : RegularFormula C ℓ
  actF_ : ActionFormula C ℓ → RegularFormula C ℓ
  _·_ _+_ : RegularFormula C ℓ → RegularFormula C ℓ → RegularFormula C ℓ
  _* _⁺ : RegularFormula C ℓ → RegularFormula C ℓ
