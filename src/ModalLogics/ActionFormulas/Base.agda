{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.ActionFormulas.Base where

open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulas using (ActionFormula; _∈_)
open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

infix 50 ~_
infix 45 ⟨_⟩_
infix 45 [_]_
infixr 40 _∧_
infixr 35 _∨_
infixr 30 _⇒_

data Formula (S : Set ℓ) : Set ℓ where
  true false : Formula S
  ~_ : Formula S → Formula S
  _∧_ _∨_ _⇒_ : Formula S → Formula S → Formula S
  ⟨_⟩_ [_]_ : ActionFormula S → Formula S → Formula S

infix 25 _⊨_

_⊨_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formula (Shape C) → Set (ℓ₁ ⊔ ℓ₂)
_ ⊨ true = ⊤
_ ⊨ false = ⊥
x ⊨ ~ f = ¬ x ⊨ f
x ⊨ f₁ ∧ f₂ = x ⊨ f₁ × x ⊨ f₂
x ⊨ f₁ ∨ f₂ = x ⊨ f₁ ⊎ x ⊨ f₂
x ⊨ f₁ ⇒ f₂ = x ⊨ f₁ → x ⊨ f₂
x ⊨ ⟨ af ⟩ f with free x
... | pure _ = ⊥
... | impure (s , c) = s ∈ af × ∃[ p ] c p ⊨ f
x ⊨ [ af ] f with free x
... | pure _ = ⊤
... | impure (s , c) = s ∈ af → ∀ p → c p ⊨ f
