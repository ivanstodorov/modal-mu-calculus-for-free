{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.HennessyMilnerLogic.Base where

open import Common.Program using (Program; ParameterizedProgram; free; pure; impure)
open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 50 ~_
infix 45 ⟨_⟩_
infix 45 [_]_
infixr 40 _∧_
infixr 35 _∨_
infixr 30 _⇒_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ~_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : Shape C → Formula C → Formula C

infix 25 _⊨_

_⊨_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formula C → Set (ℓ₁ ⊔ ℓ₂)
_ ⊨ true = ⊤
_ ⊨ false = ⊥
x ⊨ ~ f = ¬ x ⊨ f
x ⊨ f₁ ∧ f₂ = x ⊨ f₁ × x ⊨ f₂
x ⊨ f₁ ∨ f₂ = x ⊨ f₁ ⊎ x ⊨ f₂
x ⊨ f₁ ⇒ f₂ = x ⊨ f₁ → x ⊨ f₂
x ⊨ ⟨ s₁ ⟩ f with free x
... | pure _ = ⊥
... | impure (s₂ , c) = s₁ ≡ s₂ × ∃[ p ] c p ⊨ f
x ⊨ [ s₁ ] f with free x
... | pure _ = ⊤
... | impure (s₂ , c) = s₁ ≡ s₂ → ∀ p → c p ⊨ f

infix 25 _▷_⊨_

_▷_⊨_ : {C : Container ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → I → ParameterizedProgram C I O → Formula C → Set (ℓ₁ ⊔ ℓ₂)
i ▷ x ⊨ f = x i ⊨ f
