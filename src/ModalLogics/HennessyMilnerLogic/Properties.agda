{-# OPTIONS --without-K #-}
module ModalLogics.HennessyMilnerLogic.Properties where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty using () renaming (⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_∘_; const; case_of_)
open import Level using (Level; lift)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_; _⊩_〔_〕)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (Dec; yes; no; _because_)

open _⋆_
open Formula
open _≡_
open IsDecEquivalence ⦃...⦄
open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ⊩-dec : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → Dec (f ⊩ x)

⊩-decᵖ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula C) → (x : Program C I O) → (i : I) → Dec (f ⊩ x 〔 i 〕)
does ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

-- Proposition Logic

-- Theorems for ¬_

¬true⇔false : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → ¬ true ⊩ x ⇔ false ⊩ x
¬true⇔false x = forward x , backward x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → ¬ true ⊩ x → false ⊩ x
  forward _ h = ⊥-elim₀ (h tt)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → false ⊩ x → ¬ true ⊩ x
  backward _ h = ⊥-elim h

¬false⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → ¬ false ⊩ x ⇔ true ⊩ x
¬false⇔true x = forward x , backward x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → ¬ false ⊩ x → true ⊩ x
  forward _ _ = tt

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → true ⊩ x → ¬ false ⊩ x
  backward _ _ h = ⊥-elim h

¬¬f⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → ¬ ¬ f ⊩ x ⇔ f ⊩ x
¬¬f⇔f f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → ¬ ¬ f ⊩ x → f ⊩ x
  forward f x ¬¬h with ⊩-dec f x
  ... | no ¬h = ⊥-elim₀ (¬¬h ¬h)
  ... | yes h = h

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ⊩ x → ¬ ¬ f ⊩ x
  backward _ _ h ¬h = ¬h h

¬|f₁∧f₂|⇔¬f₁∨¬f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ (f₁ ∧ f₂) ⊩ x ⇔ ¬ f₁ ∨ ¬ f₂ ⊩ x
¬|f₁∧f₂|⇔¬f₁∨¬f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ (f₁ ∧ f₂) ⊩ x → ¬ f₁ ∨ ¬ f₂ ⊩ x
  forward f₁ f₂ x h with ⊩-dec f₁ x
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ with ⊩-dec f₂ x
  ...   | no ¬h₂ = inj₂ ¬h₂
  ...   | yes h₂ = ⊥-elim₀ (h (h₁ , h₂))

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ f₁ ∨ ¬ f₂ ⊩ x → ¬ (f₁ ∧ f₂) ⊩ x
  backward _ _ _ (inj₁ ¬h₁) (h₁ , _) = ⊥-elim₀ (¬h₁ h₁)
  backward _ _ _ (inj₂ ¬h₂) (_ , h₂) = ⊥-elim₀ (¬h₂ h₂)

¬|f₁∨f₂|⇔¬f₁∧¬f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ (f₁ ∨ f₂) ⊩ x ⇔ ¬ f₁ ∧ ¬ f₂ ⊩ x
¬|f₁∨f₂|⇔¬f₁∧¬f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ (f₁ ∨ f₂) ⊩ x → ¬ f₁ ∧ ¬ f₂ ⊩ x
  forward _ _ _ h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ f₁ ∧ ¬ f₂ ⊩ x → ¬ (f₁ ∨ f₂) ⊩ x
  backward _ _ _ (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
  backward _ _ _ (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for _∧_

f∧f⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ f ⊩ x ⇔ f ⊩ x
f∧f⇔f f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ f ⊩ x → f ⊩ x
  forward _ _ (h , _) = h

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ⊩ x → f ∧ f ⊩ x
  backward _ _ h = h , h

f₁∧f₂⇔f₂∧f₁ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ∧ f₂ ⊩ x ⇔ f₂ ∧ f₁ ⊩ x
f₁∧f₂⇔f₂∧f₁ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ∧ f₂ ⊩ x → f₂ ∧ f₁ ⊩ x
  forward _ _ _ (h₁ , h₂) = h₂ , h₁

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₂ ∧ f₁ ⊩ x → f₁ ∧ f₂ ⊩ x
  backward _ _ _ (h₂ , h₁) = h₁ , h₂

|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∧ f₂) ∧ f₃ ⊩ x ⇔ f₁ ∧ (f₂ ∧ f₃) ⊩ x
|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∧ f₂) ∧ f₃ ⊩ x → f₁ ∧ (f₂ ∧ f₃) ⊩ x
  forward _ _ _ _ ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∧ (f₂ ∧ f₃) ⊩ x → (f₁ ∧ f₂) ∧ f₃ ⊩ x
  backward _ _ _ _ (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∧ (f₂ ∨ f₃) ⊩ x ⇔ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x
f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∧ (f₂ ∨ f₃) ⊩ x → (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x
  forward _ _ _ _ (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
  forward _ _ _ _ (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x → f₁ ∧ (f₂ ∨ f₃) ⊩ x
  backward _ _ _ _ (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
  backward _ _ _ _ (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

f∧true⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ true ⊩ x ⇔ f ⊩ x
f∧true⇔f f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ true ⊩ x → f ⊩ x
  forward _ _ (h , _) = h

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ⊩ x → f ∧ true ⊩ x
  backward _ _ h = h , tt

f∧false⇔false : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ false ⊩ x ⇔ false ⊩ x
f∧false⇔false f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ false ⊩ x → false ⊩ x
  forward _ _ ()

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → false ⊩ x → f ∧ false ⊩ x
  backward _ _ ()

-- Theorems for _∨_

f∨f⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ f ⊩ x ⇔ f ⊩ x
f∨f⇔f f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ f ⊩ x → f ⊩ x
  forward _ _ (inj₁ h) = h
  forward _ _ (inj₂ h) = h

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ⊩ x → f ∨ f ⊩ x
  backward _ _ h = inj₁ h

f₁∨f₂⇔f₂∨f₁ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ∨ f₂ ⊩ x ⇔ f₂ ∨ f₁ ⊩ x
f₁∨f₂⇔f₂∨f₁ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ∨ f₂ ⊩ x → f₂ ∨ f₁ ⊩ x
  forward _ _ _ (inj₁ h₁) = inj₂ h₁
  forward _ _ _ (inj₂ h₂) = inj₁ h₂

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₂ ∨ f₁ ⊩ x → f₁ ∨ f₂ ⊩ x
  backward _ _ _ (inj₁ h₂) = inj₂ h₂
  backward _ _ _ (inj₂ h₁) = inj₁ h₁

|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∨ f₂) ∨ f₃ ⊩ x ⇔ f₁ ∨ (f₂ ∨ f₃) ⊩ x
|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∨ f₂) ∨ f₃ ⊩ x → f₁ ∨ (f₂ ∨ f₃) ⊩ x
  forward _ _ _ _ (inj₁ (inj₁ h₁)) = inj₁ h₁
  forward _ _ _ _ (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
  forward _ _ _ _ (inj₂ h₃) = inj₂ (inj₂ h₃)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∨ (f₂ ∨ f₃) ⊩ x → (f₁ ∨ f₂) ∨ f₃ ⊩ x
  backward _ _ _ _ (inj₁ h₁) = inj₁ (inj₁ h₁)
  backward _ _ _ _ (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
  backward _ _ _ _ (inj₂ (inj₂ h₃)) = inj₂ h₃

f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∨ (f₂ ∧ f₃) ⊩ x ⇔ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x
f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∨ (f₂ ∧ f₃) ⊩ x → (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x
  forward _ _ _ _ (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
  forward _ _ _ _ (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x → f₁ ∨ (f₂ ∧ f₃) ⊩ x
  backward _ _ _ _ (inj₁ h₁ , _) = inj₁ h₁
  backward _ _ _ _ (_ , inj₁ h₁) = inj₁ h₁
  backward _ _ _ _ (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

f∨true⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ true ⊩ x ⇔ true ⊩ x
f∨true⇔true f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ true ⊩ x → true ⊩ x
  forward _ _ _ = tt

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → true ⊩ x → f ∨ true ⊩ x
  backward _ _ _ = inj₂ tt

f∨false⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ false ⊩ x ⇔ f ⊩ x
f∨false⇔f f x = forward f x , backward f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ false ⊩ x → f ⊩ x
  forward _ _ (inj₁ h) = h

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ⊩ x → f ∨ false ⊩ x
  backward _ _ h = inj₁ h

-- Theorems for _⇒_

f₁⇒f₂⇔¬f₁∨f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ⇒ f₂ ⊩ x ⇔ ¬ f₁ ∨ f₂ ⊩ x
f₁⇒f₂⇔¬f₁∨f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ⇒ f₂ ⊩ x → ¬ f₁ ∨ f₂ ⊩ x
  forward f₁ _ x h with ⊩-dec f₁ x
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ = inj₂ (h h₁)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ¬ f₁ ∨ f₂ ⊩ x → f₁ ⇒ f₂ ⊩ x
  backward _ _ _ (inj₁ ¬h₁) h₁ = ⊥-elim₀ (¬h₁ h₁)
  backward _ _ _ (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

¬|⟨s⟩f|⇔[s]¬f : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ¬ (⟨ s ⟩ f) ⊩ x ⇔ [ s ] ¬ f ⊩ x
¬|⟨s⟩f|⇔[s]¬f s f x = forward s f x , backward s f x
  where
  forward : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ¬ (⟨ s ⟩ f) ⊩ x → [ s ] ¬ f ⊩ x
  forward _ _ (pure _) _ = tt
  forward s₁ _ (impure (s₂ , _)) h¬∃ with s₁ ≟ s₂
  ... | no _ = tt
  ... | yes refl = λ p h → h¬∃ (p , h)

  backward : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → [ s ] ¬ f ⊩ x → ¬ (⟨ s ⟩ f) ⊩ x
  backward s₁ _ (impure (s₂ , _)) _ h∃ with s₁ ≟ s₂
  ... | no _ = ⊥-elim h∃
  backward s _ (impure (.s , _)) h¬∀ (p , h) | yes refl = (h¬∀ p) h

⟨s⟩false⇔false : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → ⟨ s ⟩ false ⊩ x ⇔ false ⊩ x
⟨s⟩false⇔false s x = forward s x , backward s x
  where
  forward : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → ⟨ s ⟩ false ⊩ x → false ⊩ x
  forward s₁ (impure (s₂ , _)) h∃ with s₁ ≟ s₂
  ... | no _ = ⊥-elim h∃
  forward s (impure (.s , _)) () | yes refl

  backward : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → false ⊩ x → ⟨ s ⟩ false ⊩ x
  backward _ _ ()

⟨s⟩|f₁∨f₂|⇔⟨s⟩f₁∨⟨s⟩f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ⟨ s ⟩ (f₁ ∨ f₂) ⊩ x ⇔ ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ ⊩ x
⟨s⟩|f₁∨f₂|⇔⟨s⟩f₁∨⟨s⟩f₂ s f₁ f₂ x = forward s f₁ f₂ x , backward s f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ⟨ s ⟩ (f₁ ∨ f₂) ⊩ x → ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ ⊩ x
  forward s₁ _ _ (impure (s₂ , _)) h∃ with s₁ ≟ s₂
  ... | no _ = ⊥-elim h∃
  forward s _ _ (impure (.s , _)) (p , inj₁ h₁) | yes refl = inj₁ (p , h₁)
  forward s _ _ (impure (.s , _)) (p , inj₂ h₂) | yes refl = inj₂ (p , h₂)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ ⊩ x → ⟨ s ⟩ (f₁ ∨ f₂) ⊩ x
  backward s₁ _ _ (impure (s₂ , _)) (inj₁ h∃₁) with s₁ ≟ s₂
  ... | no _ = ⊥-elim h∃₁
  backward s _ _ (impure (.s , _)) (inj₁ (p , h₁)) | yes refl = (p , inj₁ h₁)
  backward s₁ _ _ (impure (s₂ , _)) (inj₂ h∃₂) with s₁ ≟ s₂
  ... | no _ = ⊥-elim h∃₂
  backward s _ _ (impure (.s , _)) (inj₂ (p , h₂)) | yes refl = (p , inj₂ h₂)

⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ⟨ s ⟩ f₁ ∧ [ s ] f₂ ⊩ x → ⟨ s ⟩ (f₁ ∧ f₂) ⊩ x
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| s₁ _ _ (impure (s₂ , _)) _ with s₁ ≟ s₂
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| s₁ _ _ (impure (s₂ , _)) () | no _
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| s _ _ (impure (.s , _)) ((p , h₁) , h∀₂) | yes refl = p , h₁ , h∀₂ p

-- Theorems for [_]_

¬|[s]f|⇔⟨s⟩¬f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ¬ ([ s ] f) ⊩ x ⇔ ⟨ s ⟩ ¬ f ⊩ x
¬|[s]f|⇔⟨s⟩¬f s f x = forward s f x , backward s f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ¬ ([ s ] f) ⊩ x → ⟨ s ⟩ ¬ f ⊩ x
  forward _ _ (pure _) h¬∀ = lift (h¬∀ tt)
  forward s₁ f x@(impure (s₂ , c)) h¬∀ with ⊩-dec (⟨ s₁ ⟩ ¬ f) x
  ... | yes h∃ = h∃
  ... | no h¬∃ with s₁ ≟ s₂
  ...   | no _ = lift (h¬∀ tt)
  ...   | yes refl = ⊥-elim₀ (h¬∀ λ p → case ⊩-dec f (c p) of λ { (yes h) → h ; (no ¬h) → ⊥-elim₀ (h¬∃ (p , ¬h)) })

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ⟨ s ⟩ ¬ f ⊩ x → ¬ ([ s ] f) ⊩ x
  backward s₁ _ (impure (s₂ , _)) h∃ _ with s₁ ≟ s₂
  ... | no _ = ⊥-elim h∃
  backward s _ (impure (.s , _)) (p , ¬h) h∀ | yes refl = ¬h (h∀ p)

[s]true⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → [ s ] true ⊩ x ⇔ true ⊩ x
[s]true⇔true s x = forward s x , backward s x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → [ s ] true ⊩ x → true ⊩ x
  forward _ _ _ = tt

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → true ⊩ x → [ s ] true ⊩ x
  backward _ (pure _) _ = tt
  backward s₁ (impure (s₂ , _)) _ with s₁ ≟ s₂
  ... | no _ = tt
  ... | yes refl = const tt

[s]|f₁∧f₂|⇔[s]f₁∧[s]f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → [ s ] (f₁ ∧ f₂) ⊩ x ⇔ [ s ] f₁ ∧ [ s ] f₂ ⊩ x
[s]|f₁∧f₂|⇔[s]f₁∧[s]f₂ s f₁ f₂ x = forward s f₁ f₂ x , backward s f₁ f₂ x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → [ s ] (f₁ ∧ f₂) ⊩ x → [ s ] f₁ ∧ [ s ] f₂ ⊩ x
  forward _ _ _ (pure _) _ = tt , tt
  forward s₁ _ _ (impure (s₂ , _)) h∀ with s₁ ≟ s₂
  ... | no _ = tt , tt
  ... | yes refl = (proj₁ ∘ h∀) , (proj₂ ∘ h∀)

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → [ s ] f₁ ∧ [ s ] f₂ ⊩ x → [ s ] (f₁ ∧ f₂) ⊩ x
  backward _ _ _ (pure _) _ = tt
  backward s₁ _ _ (impure (s₂ , _)) _ with s₁ ≟ s₂
  ... | no _ = tt
  backward s _ _ (impure (.s , _)) (h∀₁ , h∀₂) | yes refl = λ p → h∀₁ p , h∀₂ p

[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → [ s ] (f₁ ∨ f₂) ⊩ x → ⟨ s ⟩ f₁ ∨ [ s ] f₂ ⊩ x
[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ _ _ _ (pure _) _ = inj₂ tt
[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ s₁ f₁ f₂ x@(impure (s₂ , _)) h with ⊩-dec (⟨ s₁ ⟩ f₁) x
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊩-dec ([ s₁ ] f₂) x
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with s₁ ≟ s₂
...     | no _ = inj₂ tt
...     | yes _ = ⊥-elim₀ (h¬∀ λ p → case h p of λ { (inj₁ h₁) → ⊥-elim₀ (h¬∃ (p , h₁)) ; (inj₂ h₂) → h₂ })
