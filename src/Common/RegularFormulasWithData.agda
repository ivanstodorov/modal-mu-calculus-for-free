{-# OPTIONS --without-K --safe #-}
module Common.RegularFormulasWithData where

open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Sum using (_⊎_)
open import Level using (Level; Lift; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

private variable
  s : Level

infix 60 val_
infix 60 act_
infix 55 _ᶜ
infixr 45 _∩_
infixr 40 _∪_
infix 30 ∀⦗_⦘_
infix 30 ∃⦗_⦘_

data ActionFormula (S : Set s) (ℓ : Level) : Set (s ⊔ suc ℓ) where
  true false : ActionFormula S ℓ
  val_ : Set ℓ → ActionFormula S ℓ
  act_ : S → ActionFormula S ℓ
  _ᶜ : ActionFormula S ℓ → ActionFormula S ℓ
  _∩_ _∪_ : ActionFormula S ℓ → ActionFormula S ℓ → ActionFormula S ℓ
  ∀⦗_⦘_ ∃⦗_⦘_ : (α : Set ℓ) → (α → ActionFormula S ℓ) → ActionFormula S ℓ

infix 25 _∈_

_∈_ : {S : Set s} → {ℓ : Level} → S → ActionFormula S ℓ → Set (s ⊔ ℓ)
_ ∈ true = ⊤
_ ∈ false = ⊥
_∈_ {s = s} {ℓ = ℓ} _ (val x) = Lift (s ⊔ ℓ) x
_∈_ {s = s} {ℓ = ℓ} s₁ (act s₂) = Lift (s ⊔ ℓ) (s₁ ≡ s₂)
s ∈ af ᶜ = ¬ s ∈ af
s ∈ af₁ ∩ af₂ = s ∈ af₁ × s ∈ af₂
s ∈ af₁ ∪ af₂ = s ∈ af₁ ⊎ s ∈ af₂
s ∈ ∀⦗ _ ⦘ af = ∀ a → s ∈ af a
s ∈ ∃⦗ _ ⦘ af = ∃[ a ] s ∈ af a

infix 29 actF_
infix 28 _*
infix 27 _⁺
infixr 26 _·_
infixr 25 _+_

data RegularFormula (S : Set s) (ℓ : Level) : Set (s ⊔ suc ℓ) where
  ε : RegularFormula S ℓ
  actF_ : ActionFormula S ℓ → RegularFormula S ℓ
  _·_ _+_ : RegularFormula S ℓ → RegularFormula S ℓ → RegularFormula S ℓ
  _* _⁺ : RegularFormula S ℓ → RegularFormula S ℓ
