{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.HennessyMilnerLogic.Properties where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program; ParameterizedProgram; free; pure; impure)
open import Data.Container using (Container; Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_∘_; case_of_; const)
open import Level using (Level)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_; _⊩_〔_〕)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (Dec; yes; no; _because_)

open Formula
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl)
open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ⊩-dec : (f : Formula C) → (x : Program C α) → Dec (f ⊩ x)

⊩-decᵖ : {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula C) → (x : ParameterizedProgram C I O) → (i : I) → Dec (f ⊩ x 〔 i 〕)
does ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

-- Proposition Logic

-- Theorems for ¬_

¬true⇔false : (x : Program C α) → ¬ true ⊩ x ⇔ false ⊩ x
¬true⇔false x = forward x , backward x
  where
  forward : (x : Program C α) → ¬ true ⊩ x → false ⊩ x
  forward _ h = ⊥₀-elim (h tt)

  backward : (x : Program C α) → false ⊩ x → ¬ true ⊩ x
  backward _ = ⊥-elim

¬false⇔true : (x : Program C α) → ¬ false ⊩ x ⇔ true ⊩ x
¬false⇔true x = forward x , backward x
  where
  forward : (x : Program C α) → ¬ false ⊩ x → true ⊩ x
  forward _ _ = tt

  backward : (x : Program C α) → true ⊩ x → ¬ false ⊩ x
  backward _ _ = ⊥-elim

¬¬f⇔f : (f : Formula C) → (x : Program C α) → ¬ ¬ f ⊩ x ⇔ f ⊩ x
¬¬f⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → ¬ ¬ f ⊩ x → f ⊩ x
  forward f x ¬¬h with ⊩-dec f x
  ... | no ¬h = ⊥₀-elim (¬¬h ¬h)
  ... | yes h = h

  backward : (f : Formula C) → (x : Program C α) → f ⊩ x → ¬ ¬ f ⊩ x
  backward _ _ h ¬h = ¬h h

¬|f₁∧f₂|⇔¬f₁∨¬f₂ : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ (f₁ ∧ f₂) ⊩ x ⇔ ¬ f₁ ∨ ¬ f₂ ⊩ x
¬|f₁∧f₂|⇔¬f₁∨¬f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ (f₁ ∧ f₂) ⊩ x → ¬ f₁ ∨ ¬ f₂ ⊩ x
  forward f₁ f₂ x h with ⊩-dec f₁ x
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ with ⊩-dec f₂ x
  ...   | no ¬h₂ = inj₂ ¬h₂
  ...   | yes h₂ = ⊥₀-elim (h (h₁ , h₂))

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ f₁ ∨ ¬ f₂ ⊩ x → ¬ (f₁ ∧ f₂) ⊩ x
  backward _ _ _ (inj₁ ¬h₁) (h₁ , _) = ⊥₀-elim (¬h₁ h₁)
  backward _ _ _ (inj₂ ¬h₂) (_ , h₂) = ⊥₀-elim (¬h₂ h₂)

¬|f₁∨f₂|⇔¬f₁∧¬f₂ : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ (f₁ ∨ f₂) ⊩ x ⇔ ¬ f₁ ∧ ¬ f₂ ⊩ x
¬|f₁∨f₂|⇔¬f₁∧¬f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ (f₁ ∨ f₂) ⊩ x → ¬ f₁ ∧ ¬ f₂ ⊩ x
  forward _ _ _ h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ f₁ ∧ ¬ f₂ ⊩ x → ¬ (f₁ ∨ f₂) ⊩ x
  backward _ _ _ (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
  backward _ _ _ (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for _∧_

f∧f⇔f : (f : Formula C) → (x : Program C α) → f ∧ f ⊩ x ⇔ f ⊩ x
f∧f⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → f ∧ f ⊩ x → f ⊩ x
  forward _ _ (h , _) = h

  backward : (f : Formula C) → (x : Program C α) → f ⊩ x → f ∧ f ⊩ x
  backward _ _ h = h , h

f₁∧f₂⇔f₂∧f₁ : (f₁ f₂ : Formula C) → (x : Program C α) → f₁ ∧ f₂ ⊩ x ⇔ f₂ ∧ f₁ ⊩ x
f₁∧f₂⇔f₂∧f₁ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → f₁ ∧ f₂ ⊩ x → f₂ ∧ f₁ ⊩ x
  forward _ _ _ (h₁ , h₂) = h₂ , h₁

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → f₂ ∧ f₁ ⊩ x → f₁ ∧ f₂ ⊩ x
  backward _ _ _ (h₂ , h₁) = h₁ , h₂

|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → (f₁ ∧ f₂) ∧ f₃ ⊩ x ⇔ f₁ ∧ (f₂ ∧ f₃) ⊩ x
|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → (f₁ ∧ f₂) ∧ f₃ ⊩ x → f₁ ∧ (f₂ ∧ f₃) ⊩ x
  forward _ _ _ _ ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → f₁ ∧ (f₂ ∧ f₃) ⊩ x → (f₁ ∧ f₂) ∧ f₃ ⊩ x
  backward _ _ _ _ (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → f₁ ∧ (f₂ ∨ f₃) ⊩ x ⇔ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x
f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → f₁ ∧ (f₂ ∨ f₃) ⊩ x → (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x
  forward _ _ _ _ (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
  forward _ _ _ _ (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x → f₁ ∧ (f₂ ∨ f₃) ⊩ x
  backward _ _ _ _ (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
  backward _ _ _ _ (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

f∧true⇔f : (f : Formula C) → (x : Program C α) → f ∧ true ⊩ x ⇔ f ⊩ x
f∧true⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → f ∧ true ⊩ x → f ⊩ x
  forward _ _ (h , _) = h

  backward : (f : Formula C) → (x : Program C α) → f ⊩ x → f ∧ true ⊩ x
  backward _ _ h = h , tt

f∧false⇔false : (f : Formula C) → (x : Program C α) → f ∧ false ⊩ x ⇔ false ⊩ x
f∧false⇔false f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → f ∧ false ⊩ x → false ⊩ x
  forward _ _ ()

  backward : (f : Formula C) → (x : Program C α) → false ⊩ x → f ∧ false ⊩ x
  backward _ _ ()

-- Theorems for _∨_

f∨f⇔f : (f : Formula C) → (x : Program C α) → f ∨ f ⊩ x ⇔ f ⊩ x
f∨f⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → f ∨ f ⊩ x → f ⊩ x
  forward _ _ (inj₁ h) = h
  forward _ _ (inj₂ h) = h

  backward : (f : Formula C) → (x : Program C α) → f ⊩ x → f ∨ f ⊩ x
  backward _ _ h = inj₁ h

f₁∨f₂⇔f₂∨f₁ : (f₁ f₂ : Formula C) → (x : Program C α) → f₁ ∨ f₂ ⊩ x ⇔ f₂ ∨ f₁ ⊩ x
f₁∨f₂⇔f₂∨f₁ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → f₁ ∨ f₂ ⊩ x → f₂ ∨ f₁ ⊩ x
  forward _ _ _ (inj₁ h₁) = inj₂ h₁
  forward _ _ _ (inj₂ h₂) = inj₁ h₂

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → f₂ ∨ f₁ ⊩ x → f₁ ∨ f₂ ⊩ x
  backward _ _ _ (inj₁ h₂) = inj₂ h₂
  backward _ _ _ (inj₂ h₁) = inj₁ h₁

|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → (f₁ ∨ f₂) ∨ f₃ ⊩ x ⇔ f₁ ∨ (f₂ ∨ f₃) ⊩ x
|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → (f₁ ∨ f₂) ∨ f₃ ⊩ x → f₁ ∨ (f₂ ∨ f₃) ⊩ x
  forward _ _ _ _ (inj₁ (inj₁ h₁)) = inj₁ h₁
  forward _ _ _ _ (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
  forward _ _ _ _ (inj₂ h₃) = inj₂ (inj₂ h₃)

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → f₁ ∨ (f₂ ∨ f₃) ⊩ x → (f₁ ∨ f₂) ∨ f₃ ⊩ x
  backward _ _ _ _ (inj₁ h₁) = inj₁ (inj₁ h₁)
  backward _ _ _ _ (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
  backward _ _ _ _ (inj₂ (inj₂ h₃)) = inj₂ h₃

f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → f₁ ∨ (f₂ ∧ f₃) ⊩ x ⇔ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x
f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → f₁ ∨ (f₂ ∧ f₃) ⊩ x → (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x
  forward _ _ _ _ (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
  forward _ _ _ _ (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x → f₁ ∨ (f₂ ∧ f₃) ⊩ x
  backward _ _ _ _ (inj₁ h₁ , _) = inj₁ h₁
  backward _ _ _ _ (_ , inj₁ h₁) = inj₁ h₁
  backward _ _ _ _ (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

f∨true⇔true : (f : Formula C) → (x : Program C α) → f ∨ true ⊩ x ⇔ true ⊩ x
f∨true⇔true f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → f ∨ true ⊩ x → true ⊩ x
  forward _ _ _ = tt

  backward : (f : Formula C) → (x : Program C α) → true ⊩ x → f ∨ true ⊩ x
  backward _ _ _ = inj₂ tt

f∨false⇔f : (f : Formula C) → (x : Program C α) → f ∨ false ⊩ x ⇔ f ⊩ x
f∨false⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → f ∨ false ⊩ x → f ⊩ x
  forward _ _ (inj₁ h) = h

  backward : (f : Formula C) → (x : Program C α) → f ⊩ x → f ∨ false ⊩ x
  backward _ _ h = inj₁ h

-- Theorems for _⇒_

f₁⇒f₂⇔¬f₁∨f₂ : (f₁ f₂ : Formula C) → (x : Program C α) → f₁ ⇒ f₂ ⊩ x ⇔ ¬ f₁ ∨ f₂ ⊩ x
f₁⇒f₂⇔¬f₁∨f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → f₁ ⇒ f₂ ⊩ x → ¬ f₁ ∨ f₂ ⊩ x
  forward f₁ _ x h with ⊩-dec f₁ x
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ = inj₂ (h h₁)

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → ¬ f₁ ∨ f₂ ⊩ x → f₁ ⇒ f₂ ⊩ x
  backward _ _ _ (inj₁ ¬h₁) h₁ = ⊥₀-elim (¬h₁ h₁)
  backward _ _ _ (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

-- Without ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄

⟨s⟩false⇔false : (s : Shape C) → (x : Program C α) → ⟨ s ⟩ false ⊩ x ⇔ false ⊩ x
⟨s⟩false⇔false s x = forward s x , backward s x
  where
  forward : (s : Shape C) → (x : Program C α) → ⟨ s ⟩ false ⊩ x → false ⊩ x
  forward s₁ x h∃ with free x
  ... | pure _ = h∃
  forward s₁ x () | impure (s₂ , c)

  backward : (s : Shape C) → (x : Program C α) → false ⊩ x → ⟨ s ⟩ false ⊩ x
  backward _ _ ()

⟨s⟩|f₁∨f₂|⇔⟨s⟩f₁∨⟨s⟩f₂ : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → ⟨ s ⟩ (f₁ ∨ f₂) ⊩ x ⇔ ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ ⊩ x
⟨s⟩|f₁∨f₂|⇔⟨s⟩f₁∨⟨s⟩f₂ s f₁ f₂ x = forward s f₁ f₂ x , backward s f₁ f₂ x
  where
  forward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → ⟨ s ⟩ (f₁ ∨ f₂) ⊩ x → ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ ⊩ x
  forward s₁ _ _ x h∃ with free x
  forward s₂ _ _ x (refl , p , inj₁ h₁) | impure (s₂ , c) = inj₁ (refl , p , h₁)
  forward s₂ _ _ x (refl , p , inj₂ h₂) | impure (s₂ , c) = inj₂ (refl , p , h₂)

  backward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ ⊩ x → ⟨ s ⟩ (f₁ ∨ f₂) ⊩ x
  backward s₁ _ _ x h∃ with free x
  backward s₁ _ _ x (inj₁ ()) | pure _
  backward s₁ _ _ x (inj₂ ()) | pure _
  backward s₂ _ _ x (inj₁ (refl , p , h₁)) | impure (s₂ , c) = refl , p , inj₁ h₁
  backward s₂ _ _ x (inj₂ (refl , p , h₂)) | impure (s₂ , c) = refl , p , inj₂ h₂

⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → ⟨ s ⟩ f₁ ∧ [ s ] f₂ ⊩ x → ⟨ s ⟩ (f₁ ∧ f₂) ⊩ x
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| s₁ _ _ x h with free x
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| s₂ _ _ x ((refl , p , h₁) , inj₁ (_ , h∀₂)) | impure (s₂ , c) = refl , p , h₁ , h∀₂ p
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| s₂ _ _ x ((refl , _) , inj₂ h) | impure (s₂ , c) = ⊥₀-elim (h refl)

-- With ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄

¬|⟨s⟩f|⇔[s]¬f : ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : Program C α) → ¬ (⟨ s ⟩ f) ⊩ x ⇔ [ s ] ¬ f ⊩ x
¬|⟨s⟩f|⇔[s]¬f s f x = forward s f x , backward s f x
  where
  forward : ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : Program C α) → ¬ (⟨ s ⟩ f) ⊩ x → [ s ] ¬ f ⊩ x
  forward s₁ _ x h¬∃ with free x
  ... | pure _ = tt
  ... | impure (s₂ , c) with s₁ ≟ s₂
  ...   | no h = inj₂ h
  ...   | yes refl = inj₁ (refl , λ p h → h¬∃ (refl , p , h))

  backward : ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : Program C α) → [ s ] ¬ f ⊩ x → ¬ (⟨ s ⟩ f) ⊩ x
  backward s₁ _ x h¬∀ h∃ with free x
  backward s₁ _ x h¬∀ () | pure _
  backward s₂ _ x (inj₁ (_ , h¬∀)) (refl , p , h) | impure (s₂ , c) = h¬∀ p h
  backward s₂ _ x (inj₂ h) (refl , _) | impure (s₂ , c) = h refl

-- Theorems for [_]_

-- Without ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄

[s]|f₁∧f₂|⇔[s]f₁∧[s]f₂ : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → [ s ] (f₁ ∧ f₂) ⊩ x ⇔ [ s ] f₁ ∧ [ s ] f₂ ⊩ x
[s]|f₁∧f₂|⇔[s]f₁∧[s]f₂ s f₁ f₂ x = forward s f₁ f₂ x , backward s f₁ f₂ x
  where
  forward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → [ s ] (f₁ ∧ f₂) ⊩ x → [ s ] f₁ ∧ [ s ] f₂ ⊩ x
  forward s₁ _ _ x h∀ with free x
  ... | pure _ = tt , tt
  forward .s₂ _ _ x (inj₁ (refl , h∀)) | impure (s₂ , c) = inj₁ (refl , proj₁ ∘ h∀) , inj₁ (refl , proj₂ ∘ h∀)
  forward s₁ _ _ x (inj₂ h) | impure (s₂ , c) = inj₂ h , inj₂ h

  backward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → [ s ] f₁ ∧ [ s ] f₂ ⊩ x → [ s ] (f₁ ∧ f₂) ⊩ x
  backward s₁ _ _ x (h∀₁ , h∀₂) with free x
  ... | pure _ = tt
  backward .s₂ _ _ x (inj₁ (refl , h∀₁) , inj₁ (_ , h∀₂)) | impure (s₂ , c) = inj₁ (refl , λ p → h∀₁ p , h∀₂ p)
  backward s₁ _ _ x (inj₂ h , _) | impure (s₂ , c) = inj₂ h
  backward s₁ _ _ x (_ , inj₂ h) | impure (s₂ , c) = inj₂ h

[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → [ s ] (f₁ ∨ f₂) ⊩ x → ⟨ s ⟩ f₁ ∨ [ s ] f₂ ⊩ x
[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ s₁ f₁ f₂ x h with ⊩-dec (⟨ s₁ ⟩ f₁) x
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊩-dec ([ s₁ ] f₂) x
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with free x
...     | pure _ = inj₂ tt
[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ .s₂ f₁ f₂ x (inj₁ (refl , h)) | no h¬∃ | no h¬∀ | impure (s₂ , c) = ⊥₀-elim (h¬∀ (inj₁ (refl , λ p → case h p of λ where
  (inj₁ h₁) → ⊥₀-elim (h¬∃ (refl , p , h₁))
  (inj₂ h₂) → h₂)))
[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ s₁ f₁ f₂ x (inj₂ h) | no h¬∃ | no h¬∀ | impure (s₂ , c) = inj₂ (inj₂ h)

-- With ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄

¬|[s]f|⇔⟨s⟩¬f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : Program C α) → ¬ ([ s ] f) ⊩ x ⇔ ⟨ s ⟩ ¬ f ⊩ x
¬|[s]f|⇔⟨s⟩¬f s f x = forward s f x , backward s f x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : Program C α) → ¬ ([ s ] f) ⊩ x → ⟨ s ⟩ ¬ f ⊩ x
  forward s₁ f x h¬∀ with ⊩-dec (⟨ s₁ ⟩ ¬ f) x
  ... | yes h∃ = h∃
  ... | no h¬∃ with free x
  ...   | pure _ = ⊥₀-elim (h¬∀ tt)
  ...   | impure (s₂ , c) with s₁ ≟ s₂
  ...     | no h = ⊥₀-elim (h¬∀ (inj₂ h))
  ...     | yes refl = refl , ⊥₀-elim (h¬∀ (inj₁ (refl , λ p → case ⊩-dec f (c p) of λ where
            (no ¬h) → ⊥₀-elim (h¬∃ (refl , p , ¬h))
            (yes h) → h)))

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : Program C α) → ⟨ s ⟩ ¬ f ⊩ x → ¬ ([ s ] f) ⊩ x
  backward s₁ _ x h∃ h∀ with free x
  backward s₂ _ x (_ , p , ¬h) (inj₁ (refl , h∀)) | impure (s₂ , c) = ¬h (h∀ p)
  backward .s₂ _ x (refl , _) (inj₂ h) | impure (s₂ , c) = h refl

[s]true⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : Program C α) → [ s ] true ⊩ x ⇔ true ⊩ x
[s]true⇔true s x = forward s x , backward s x
  where
  forward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : Program C α) → [ s ] true ⊩ x → true ⊩ x
  forward _ _ _ = tt

  backward : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : Program C α) → true ⊩ x → [ s ] true ⊩ x
  backward s₁ x _ with free x
  ... | pure _ = tt
  ... | impure (s₂ , c) with s₁ ≟ s₂
  ...   | no h = inj₂ h
  ...   | yes refl = inj₁ (refl , const tt)
