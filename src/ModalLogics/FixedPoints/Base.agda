{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.FixedPoints.Base where

open import Common.FixedPoints using (FixedPoint; IndexedContainer; WI; MI)
open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (¬_; yes; no)

open _⋆_
open IsDecEquivalence ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_
infix 30 μ_+_
infix 30 ν_+_

data Formula (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  true false : Formula C α
  ~_ : Formula C α → Formula C α
  _∧_ _∨_ _⇒_ : Formula C α → Formula C α → Formula C α
  ⟨_⟩_ [_]_ : Shape C → Formula C α → Formula C α
  μ_+_ ν_+_ : IndexedContainer (C ⋆ α) → List (FixedPoint × IndexedContainer (C ⋆ α)) → Formula C α

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C α → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
true ⊩ _ = ⊤
false ⊩ _ = ⊥
~ f ⊩ x = ¬ f ⊩ x
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
μ C + Cs ⊩ x = WI C Cs x
ν C + Cs ⊩ x = MI C Cs x

infix 25 _!_⊩_

_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → Formula C (O i) → Program C I O → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
i ! f ⊩ x = f ⊩ x i

infix 25 _▸_!_⊩_

_▸_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → (i : I) → Formula C (Maybe (O i)) → RecursiveProgram C I O → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
n ▸ i ! f ⊩ x = f ⊩ (recursionHandler x n) i
