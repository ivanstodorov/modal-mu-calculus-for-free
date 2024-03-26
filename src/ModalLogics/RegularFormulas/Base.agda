{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.RegularFormulas.Base where

open import Common.RegularFormulas using (RegularFormula; RegularFormula⁺; rf→rf⁺)
open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Bool using (true; false)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; toℕ; inject₁)
open import Data.List using (List; length; findIndexᵇ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.String using (String; _==_)
open import Level using (Level; _⊔_)
open import ModalLogics.FixedPoints.Base using (Formulaⁱ; _⊩ⁱ_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)

open RegularFormula⁺
open Fin
open List
open Formulaⁱ

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 45 ref_
infix 40 ¬_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_
infix 30 μ_．_
infix 30 ν_．_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ¬_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : RegularFormula C → Formula C → Formula C
  μ_．_ ν_．_ : String → Formula C → Formula C
  ref_ : String → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ⊩ x = f→fⁱ f [] ⊩ⁱ x
  where
  ref⁺ : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formulaⁱ C n → Formulaⁱ C (suc n)
  ref⁺ fⁱ = ref⁺' fⁱ zero
    where
    ref⁺' : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formulaⁱ C n → Fin (suc n) → Formulaⁱ C (suc n)
    ref⁺' trueⁱ _ = trueⁱ
    ref⁺' falseⁱ _ = falseⁱ
    ref⁺' (¬ⁱ fⁱ) x = ¬ⁱ ref⁺' fⁱ x
    ref⁺' (fⁱ₁ ∧ⁱ fⁱ₂) x = ref⁺' fⁱ₁ x ∧ⁱ ref⁺' fⁱ₂ x
    ref⁺' (fⁱ₁ ∨ⁱ fⁱ₂) x = ref⁺' fⁱ₁ x ∨ⁱ ref⁺' fⁱ₂ x
    ref⁺' (fⁱ₁ ⇒ⁱ fⁱ₂) x = ref⁺' fⁱ₁ x ⇒ⁱ ref⁺' fⁱ₂ x
    ref⁺' (⟨ af ⟩ⁱ fⁱ) x = ⟨ af ⟩ⁱ ref⁺' fⁱ x
    ref⁺' ([ af ]ⁱ fⁱ) x = [ af ]ⁱ ref⁺' fⁱ x
    ref⁺' (μⁱ fⁱ) x = μⁱ ref⁺' fⁱ (suc x)
    ref⁺' (νⁱ fⁱ) x = νⁱ ref⁺' fⁱ (suc x)
    ref⁺' (refⁱ i) x with toℕ i <ᵇ toℕ x
    ... | false = refⁱ inject₁⁺ i
      where
      inject₁⁺ : {n : ℕ} → Fin n → Fin (suc n)
      inject₁⁺ zero = suc zero
      inject₁⁺ (suc n) = suc (inject₁⁺ n)
    ... | true = refⁱ inject₁ i

  f→fⁱ : {C : Container ℓ₁ ℓ₂} → Formula C → (xs : List String) → Formulaⁱ C (length xs)
  f→fⁱ true _ = trueⁱ
  f→fⁱ false _ = falseⁱ
  f→fⁱ (¬ f) xs = ¬ⁱ f→fⁱ f xs
  f→fⁱ (f₁ ∧ f₂) xs = f→fⁱ f₁ xs ∧ⁱ f→fⁱ f₂ xs
  f→fⁱ (f₁ ∨ f₂) xs = f→fⁱ f₁ xs ∨ⁱ f→fⁱ f₂ xs
  f→fⁱ (f₁ ⇒ f₂) xs = f→fⁱ f₁ xs ⇒ⁱ f→fⁱ f₂ xs
  f→fⁱ (⟨ rf ⟩ f) xs = helper-∃ (rf→rf⁺ rf) (f→fⁱ f xs)
    where
    helper-∃ : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → RegularFormula⁺ C → Formulaⁱ C n → Formulaⁱ C n
    helper-∃ ε fⁱ = fⁱ
    helper-∃ (actF af) fⁱ = ⟨ af ⟩ⁱ fⁱ
    helper-∃ (rf⁺₁ · rf⁺₂) fⁱ = helper-∃ rf⁺₁ (helper-∃ rf⁺₂ fⁱ)
    helper-∃ (rf⁺₁ + rf⁺₂) fⁱ = helper-∃ rf⁺₁ fⁱ ∨ⁱ helper-∃ rf⁺₂ fⁱ
    helper-∃ (rf⁺ *) fⁱ = μⁱ helper-∃ rf⁺ (refⁱ zero) ∨ⁱ ref⁺ fⁱ
  f→fⁱ ([ rf ] f) xs = helper-∀ (rf→rf⁺ rf) (f→fⁱ f xs)
    where
    helper-∀ : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → RegularFormula⁺ C → Formulaⁱ C n → Formulaⁱ C n
    helper-∀ ε fⁱ = fⁱ
    helper-∀ (actF af) fⁱ = [ af ]ⁱ fⁱ
    helper-∀ (rf⁺₁ · rf⁺₂) fⁱ = helper-∀ rf⁺₁ (helper-∀ rf⁺₂ fⁱ)
    helper-∀ (rf⁺₁ + rf⁺₂) fⁱ = helper-∀ rf⁺₁ fⁱ ∨ⁱ helper-∀ rf⁺₂ fⁱ
    helper-∀ (rf⁺ *) fⁱ = νⁱ helper-∀ rf⁺ (refⁱ zero) ∧ⁱ ref⁺ fⁱ
  f→fⁱ (μ x ． f) xs = μⁱ f→fⁱ f (x ∷ xs)
  f→fⁱ (ν x ． f) xs = νⁱ f→fⁱ f (x ∷ xs)
  f→fⁱ (ref x) xs with findIndexᵇ (_==_ x) xs
  ... | just i = refⁱ i
  ... | nothing = falseⁱ

infix 25 _⊩_!_

_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C → Program C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
f ⊩ x ! i = f ⊩ (x i)

infix 25 _▸_⊩_!_

_▸_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula C → RecursiveProgram C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
n ▸ f ⊩ x ! i = f ⊩ (recursionHandler x n) i
