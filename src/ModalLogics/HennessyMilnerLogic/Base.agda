{-# OPTIONS --without-K #-}
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
open import Relation.Nullary using (¬_; yes; no; _because_; Dec)

open _⋆_
open IsDecEquivalence ⦃...⦄
open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ~_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : Shape C → Formula C → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set ℓ₂
true ⊩ _ = ⊤
false ⊩ _ = ⊥
(~ f) ⊩ x = ¬ (f ⊩ x)
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

postulate
  ⊩-dec : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → (f : Formula C) → (x : C ⋆ α) → Dec (f ⊩ x)

infix 25 _!_⊩_

_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → I → Formula C → Program C I O → Set ℓ₂
i ! f ⊩ x = f ⊩ (x i)

⊩-decP : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → (f : Formula C) → (x : Program C I O) → Dec (i ! f ⊩ x)
does ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

infix 25 _▸_!_⊩_

_▸_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → I → Formula C → RecursiveProgram C I O → Set ℓ₂
n ▸ i ! f ⊩ x = f ⊩ (recursionHandler x n) i

⊩-decR : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (i : I) → (f : Formula C) → (x : RecursiveProgram C I O) → Dec (n ▸ i ! f ⊩ x)
does ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | _ because proof = proof
