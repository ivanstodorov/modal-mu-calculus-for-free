{-# OPTIONS --without-K --guardedness #-}
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
open import Relation.Nullary using (¬_; yes; no; _because_; Dec)

open _⋆_
open IsDecEquivalence ⦃...⦄
open Dec ⦃...⦄

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_
infix 30 μ_+_
infix 30 ν_+_

data Formula (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) (ℓ₄ ℓ₅ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)) where
  true false : Formula C α ℓ₄ ℓ₅
  ~_ : Formula C α ℓ₄ ℓ₅ → Formula C α ℓ₄ ℓ₅
  _∧_ _∨_ _⇒_ : Formula C α ℓ₄ ℓ₅ → Formula C α ℓ₄ ℓ₅ → Formula C α ℓ₄ ℓ₅
  ⟨_⟩_ [_]_ : Shape C → Formula C α ℓ₄ ℓ₅ → Formula C α ℓ₄ ℓ₅
  μ_+_ ν_+_ : IndexedContainer (C ⋆ α) ℓ₄ ℓ₅ → List (FixedPoint × IndexedContainer (C ⋆ α) ℓ₄ ℓ₅) → Formula C α ℓ₄ ℓ₅

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C α ℓ₄ ℓ₅ → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
true ⊩ _ = ⊤
false ⊩ _ = ⊥
(~ f) ⊩ x = ¬ f ⊩ x
(f₁ ∧ f₂) ⊩ x = f₁ ⊩ x × f₂ ⊩ x
(f₁ ∨ f₂) ⊩ x = f₁ ⊩ x ⊎ f₂ ⊩ x
(f₁ ⇒ f₂) ⊩ x = f₁ ⊩ x → f₂ ⊩ x
(⟨ _ ⟩ _) ⊩ pure _ = ⊥
(⟨ s₁ ⟩ f) ⊩ impure (s₂ , c) with s₁ ≟ s₂
... | no _ = ⊥
... | yes _ = ∃[ p ] f ⊩ c p
([ _ ] _) ⊩ pure _ = ⊤
([ s₁ ] f) ⊩ impure (s₂ , c) with s₁ ≟ s₂
... | no _ = ⊤
... | yes _ = ∀ p → f ⊩ c p
(μ C + Cs) ⊩ x = WI C Cs x
(ν C + Cs) ⊩ x = MI C Cs x

postulate
  ⊩-dec : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → (f : Formula C α ℓ₄ ℓ₅) → (x : C ⋆ α) → Dec (f ⊩ x)

infix 25 _!_⊩_

_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → Formula C (O i) ℓ₅ ℓ₆ → Program C I O → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)
i ! f ⊩ x = f ⊩ x i

⊩-decP : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → (f : Formula C (O i) ℓ₅ ℓ₆) → (x : Program C I O) → Dec (i ! f ⊩ x)
does ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

infix 25 _▸_!_⊩_

_▸_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → (i : I) → Formula C (Maybe (O i)) ℓ₅ ℓ₆ → RecursiveProgram C I O → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)
n ▸ i ! f ⊩ x = f ⊩ (recursionHandler x n) i

⊩-decR : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (i : I) → (f : Formula C (Maybe (O i)) ℓ₅ ℓ₆) → (x : RecursiveProgram C I O) → Dec (n ▸ i ! f ⊩ x)
does ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | _ because proof = proof
