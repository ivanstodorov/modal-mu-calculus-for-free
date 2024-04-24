{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.ActionFormulas.Base where

open import Common.Program using (Program; ParameterizedProgram; free; pure; impure)
open import Common.RegularFormulas using (ActionFormula) renaming (_⊩_ to _⊩ᵃᶠ_)
open import Data.Container using (Container)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; _⊔_)
open import Relation.Nullary using () renaming (¬_ to ¬ˢᵗᵈ_)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 50 ¬_
infix 45 ⟨_⟩_
infix 45 [_]_
infixr 40 _∧_
infixr 35 _∨_
infixr 30 _⇒_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ¬_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : ActionFormula C → Formula C → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Formula C → Program C α → Set (ℓ₁ ⊔ ℓ₂)
true ⊩ _ = ⊤
false ⊩ _ = ⊥
¬ f ⊩ x = ¬ˢᵗᵈ f ⊩ x
f₁ ∧ f₂ ⊩ x = f₁ ⊩ x × f₂ ⊩ x
f₁ ∨ f₂ ⊩ x = f₁ ⊩ x ⊎ f₂ ⊩ x
f₁ ⇒ f₂ ⊩ x = f₁ ⊩ x → f₂ ⊩ x
⟨ af ⟩ f ⊩ x with free x
... | pure _ = ⊥
... | impure (s , c) = af ⊩ᵃᶠ s × ∃[ p ] f ⊩ c p
[ af ] f ⊩ x with free x
... | pure _ = ⊤
... | impure (s , c) = af ⊩ᵃᶠ s × (∀ p → f ⊩ c p) ⊎ ¬ˢᵗᵈ af ⊩ᵃᶠ s

infix 25 _⊩_〔_〕

_⊩_〔_〕 : {C : Container ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C → ParameterizedProgram C I O → I → Set (ℓ₁ ⊔ ℓ₂)
f ⊩ x 〔 i 〕 = f ⊩ (x i)
