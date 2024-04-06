{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.RegularFormulas.Properties where

open import Common.Program using (Program)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Nat using (ℕ)
open import Level using (Level)
open import ModalLogics.RegularFormulas.Base using (Formula; _⊩_; _⊩_〔_〕)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (Dec; _because_)

open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

postulate
  ⊩-dec : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → (f : Formula C) → (x : C ⋆ α) → Dec (f ⊩ x)

⊩-decᵖ : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula C) → (x : Program C I O) → (i : I) → Dec (f ⊩ x 〔 i 〕)
does ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | _ because proof = proof
