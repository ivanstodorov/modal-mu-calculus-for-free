{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.DataParameters.Properties where

open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Level using (Level)
open import ModalLogics.DataParameters.Base using (Formula; _⊩_; _⊩_〔_〕; _▷_⊩_〔_〕)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (Dec; _because_)

open Dec ⦃...⦄

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃
  αs : List (Set ℓ ⊎ Set ℓ)

postulate
  ⊩-dec : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C ℓ αs) → (x : C ⋆ α) → Dec (f ⊩ x)

⊩-decᵖ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula C ℓ αs) → (x : Program C I O) → (i : I) → Dec (f ⊩ x 〔 i 〕)
does ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

⊩-decʳ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (f : Formula C ℓ αs) → (x : RecursiveProgram C I O) → (i : I) → Dec (n ▷ f ⊩ x 〔 i 〕)
does ⦃ ⊩-decʳ n f x i ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊩-decʳ n f x i ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | _ because proof = proof
