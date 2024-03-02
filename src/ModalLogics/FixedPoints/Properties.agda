{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.FixedPoints.Properties where

open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Level using (Level)
open import ModalLogics.FixedPoints.Base using (Formula; _⊩_; _!_⊩_; _▸_!_⊩_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (_because_; Dec)

open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ⊩-dec : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C α) → (x : C ⋆ α) → Dec (f ⊩ x)

⊩-decP : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → (f : Formula C (O i)) → (x : Program C I O) → Dec (i ! f ⊩ x)
does ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

⊩-decR : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (i : I) → (f : Formula C (Maybe (O i))) → (x : RecursiveProgram C I O) → Dec (n ▸ i ! f ⊩ x)
does ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | _ because proof = proof
