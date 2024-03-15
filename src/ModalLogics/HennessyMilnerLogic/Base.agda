{-# OPTIONS --without-K --safe #-}
module ModalLogics.HennessyMilnerLogic.Base where

open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬'_)

open _⋆_
open IsDecEquivalence ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 40 ¬_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ¬_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : Shape C → Formula C → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set ℓ₂
true ⊩ _ = ⊤
false ⊩ _ = ⊥
¬ f ⊩ x = ¬' f ⊩ x
f₁ ∧ f₂ ⊩ x = f₁ ⊩ x × f₂ ⊩ x
f₁ ∨ f₂ ⊩ x = f₁ ⊩ x ⊎ f₂ ⊩ x
f₁ ⇒ f₂ ⊩ x = f₁ ⊩ x → f₂ ⊩ x
⟨ _ ⟩ _ ⊩ pure _ = ⊥
⟨ s₁ ⟩ f ⊩ impure (s₂ , c) with s₁ ≟ s₂
... | no _ = ⊥
... | yes _ = ∃[ p ] f ⊩ c p
[ _ ] _ ⊩ pure _ = ⊤
[ s₁ ] f ⊩ impure (s₂ , c) with s₁ ≟ s₂
... | no _ = ⊤
... | yes _ = ∀ p → f ⊩ c p

infix 25 _⊩_!_

_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C → Program C I O → I → Set ℓ₂
f ⊩ x ! i = f ⊩ (x i)

infix 25 _▸_⊩_!_

_▸_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula C → RecursiveProgram C I O → I → Set ℓ₂
n ▸ f ⊩ x ! i = f ⊩ (recursionHandler x n) i
