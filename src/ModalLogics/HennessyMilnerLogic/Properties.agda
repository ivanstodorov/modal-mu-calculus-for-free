{-# OPTIONS --without-K #-}
module ModalLogics.HennessyMilnerLogic.Properties where

open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Common.Utils using (_⇔_)
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
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_; _⊩_!_; _▸_⊩_!_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (Dec; yes; no; _because_)

open _⇔_
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

⊩-decP : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula C) → (x : Program C I O) → (i : I) → Dec (f ⊩ x ! i)
does ⦃ ⊩-decP f x i ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decP f x i ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

⊩-decR : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (f : Formula C) → (x : RecursiveProgram C I O) → (i : I) → Dec (n ▸ f ⊩ x ! i)
does ⦃ ⊩-decR n f x i ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊩-decR n f x i ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | _ because proof = proof

-- Proposition Logic

-- Theorems for ~_

~true⇔false : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → ~ true ⊩ x ⇔ false ⊩ x
to (~true⇔false _) h = ⊥-elim₀ (h tt)
from (~true⇔false _) h = ⊥-elim h

~false⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (x : C ⋆ α) → ~ false ⊩ x ⇔ true ⊩ x
to (~false⇔true _) _ = tt
from (~false⇔true _) _ h = ⊥-elim h

~~f⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → ~ ~ f ⊩ x ⇔ f ⊩ x
to (~~f⇔f f x) ¬¬h with ⊩-dec f x
... | no ¬h = ⊥-elim₀ (¬¬h ¬h)
... | yes h = h
from (~~f⇔f _ _) h ¬h = ¬h h

~|f₁∧f₂|⇔~f₁∨~f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ~ (f₁ ∧ f₂) ⊩ x ⇔ ~ f₁ ∨ ~ f₂ ⊩ x
to (~|f₁∧f₂|⇔~f₁∨~f₂ f₁ f₂ x) h with ⊩-dec f₁ x
... | no ¬h₁ = inj₁ ¬h₁
... | yes h₁ with ⊩-dec f₂ x
...   | no ¬h₂ = inj₂ ¬h₂
...   | yes h₂ = ⊥-elim₀ (h (h₁ , h₂))
from (~|f₁∧f₂|⇔~f₁∨~f₂ _ _ _) (inj₁ ¬h₁) (h₁ , _) = ⊥-elim₀ (¬h₁ h₁)
from (~|f₁∧f₂|⇔~f₁∨~f₂ _ _ _) (inj₂ ¬h₂) (_ , h₂) = ⊥-elim₀ (¬h₂ h₂)

~|f₁∨f₂|⇔~f₁∧~f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ~ (f₁ ∨ f₂) ⊩ x ⇔ ~ f₁ ∧ ~ f₂ ⊩ x
to (~|f₁∨f₂|⇔~f₁∧~f₂ _ _ _) h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)
from (~|f₁∨f₂|⇔~f₁∧~f₂ _ _ _) (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
from (~|f₁∨f₂|⇔~f₁∧~f₂ _ _ _) (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for _∧_

f∧f⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ f ⊩ x ⇔ f ⊩ x
to (f∧f⇔f _ _) (h , _) = h
from (f∧f⇔f _ _) h = h , h

f₁∧f₂⇔f₂∧f₁ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ∧ f₂ ⊩ x ⇔ f₂ ∧ f₁ ⊩ x
to (f₁∧f₂⇔f₂∧f₁ _ _ _) (h₁ , h₂) = h₂ , h₁
from (f₁∧f₂⇔f₂∧f₁ _ _ _) (h₂ , h₁) = h₁ , h₂

|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∧ f₂) ∧ f₃ ⊩ x ⇔ f₁ ∧ (f₂ ∧ f₃) ⊩ x
to (|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| _ _ _ _) ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃
from (|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| _ _ _ _) (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∧ (f₂ ∨ f₃) ⊩ x ⇔ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊩ x
to (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
to (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)
from (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
from (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

f∧true⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ true ⊩ x ⇔ f ⊩ x
to (f∧true⇔f _ _) (h , _) = h
from (f∧true⇔f _ _) h = h , tt

f∧false⇔false : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∧ false ⊩ x ⇔ false ⊩ x
to (f∧false⇔false _ _) ()
from (f∧false⇔false _ _) ()

-- Theorems for _∨_

f∨f⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ f ⊩ x ⇔ f ⊩ x
to (f∨f⇔f _ _) (inj₁ h) = h
to (f∨f⇔f _ _) (inj₂ h) = h
from (f∨f⇔f _ _) h = inj₁ h

f₁∨f₂⇔f₂∨f₁ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ∨ f₂ ⊩ x ⇔ f₂ ∨ f₁ ⊩ x
to (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₁ h₁) = inj₂ h₁
to (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₂ h₂) = inj₁ h₂
from (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₁ h₂) = inj₂ h₂
from (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₂ h₁) = inj₁ h₁

|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → (f₁ ∨ f₂) ∨ f₃ ⊩ x ⇔ f₁ ∨ (f₂ ∨ f₃) ⊩ x
to (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₁ (inj₁ h₁)) = inj₁ h₁
to (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
to (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₂ h₃) = inj₂ (inj₂ h₃)
from (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₁ h₁) = inj₁ (inj₁ h₁)
from (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
from (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₂ (inj₂ h₃)) = inj₂ h₃

f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ f₃ : Formula C) → (x : C ⋆ α) → f₁ ∨ (f₂ ∧ f₃) ⊩ x ⇔ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊩ x
to (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
to (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃
from (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₁ h₁ , _) = inj₁ h₁
from (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (_ , inj₁ h₁) = inj₁ h₁
from (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

f∨true⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ true ⊩ x ⇔ true ⊩ x
to (f∨true⇔true _ _) _ = tt
from (f∨true⇔true _ _) _ = inj₂ tt

f∨false⇔f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f : Formula C) → (x : C ⋆ α) → f ∨ false ⊩ x ⇔ f ⊩ x
to (f∨false⇔f _ _) (inj₁ h) = h
from (f∨false⇔f _ _) h = inj₁ h

-- Theorems for _⇒_

f₁⇒f₂⇔~f₁∨f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (f₁ f₂ : Formula C) → (x : C ⋆ α) → f₁ ⇒ f₂ ⊩ x ⇔ ~ f₁ ∨ f₂ ⊩ x
to (f₁⇒f₂⇔~f₁∨f₂ f₁ _ x) h with ⊩-dec f₁ x
... | no ¬h₁ = inj₁ ¬h₁
... | yes h₁ = inj₂ (h h₁)
from (f₁⇒f₂⇔~f₁∨f₂ _ _ _) (inj₁ ¬h₁) h₁ = ⊥-elim₀ (¬h₁ h₁)
from (f₁⇒f₂⇔~f₁∨f₂ _ _ _) (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

~|⟨s⟩f|⇔[s]~f : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ~ (⟨ s ⟩ f) ⊩ x ⇔ [ s ] ~ f ⊩ x
to (~|⟨s⟩f|⇔[s]~f _ _ (pure _)) _ = tt
to (~|⟨s⟩f|⇔[s]~f s₁ _ (impure (s₂ , _))) h¬∃ with s₁ ≟ s₂
... | no _ = tt
... | yes refl = λ p h → h¬∃ (p , h)
from (~|⟨s⟩f|⇔[s]~f s₁ _ (impure (s₂ , _))) _ h∃ with s₁ ≟ s₂
... | no _ = ⊥-elim h∃
from (~|⟨s⟩f|⇔[s]~f s _ (impure (.s , _))) h¬∀ (p , h) | yes refl = (h¬∀ p) h

⟨s⟩false⇔false : ⦃ eq : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → ⟨ s ⟩ false ⊩ x ⇔ false ⊩ x
to (⟨s⟩false⇔false s₁ (impure (s₂ , _))) h∃ with s₁ ≟ s₂
... | no _ = ⊥-elim h∃
to (⟨s⟩false⇔false s (impure (.s , _))) () | yes refl
from (⟨s⟩false⇔false _ _) ()

⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → ⟨ s ⟩ f₁ ∨ f₂ ⊩ x ⇔ (⟨ s ⟩ f₁) ∨ (⟨ s ⟩ f₂) ⊩ x
to (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s₁ _ _ (impure (s₂ , _))) h∃ with s₁ ≟ s₂
... | no _ = ⊥-elim h∃
to (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s _ _ (impure (.s , _))) (p , inj₁ h₁) | yes refl = inj₁ (p , h₁)
to (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s _ _ (impure (.s , _))) (p , inj₂ h₂) | yes refl = inj₂ (p , h₂)
from (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s₁ _ _ (impure (s₂ , _))) (inj₁ h∃₁) with s₁ ≟ s₂
... | no _ = ⊥-elim h∃₁
from (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s _ _ (impure (.s , _))) (inj₁ (p , h₁)) | yes refl = (p , inj₁ h₁)
from (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s₁ _ _ (impure (s₂ , _))) (inj₂ h∃₂) with s₁ ≟ s₂
... | no _ = ⊥-elim h∃₂
from (⟨s⟩f₁∨f₂⇔|⟨s⟩f₁|∨|⟨s⟩f₂| s _ _ (impure (.s , _))) (inj₂ (p , h₂)) | yes refl = (p , inj₂ h₂)

|⟨s⟩f₁|∧|[s]f₂|→⟨s⟩f₁∧f₂ : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → (⟨ s ⟩ f₁) ∧ ([ s ] f₂) ⊩ x → ⟨ s ⟩ f₁ ∧ f₂ ⊩ x
|⟨s⟩f₁|∧|[s]f₂|→⟨s⟩f₁∧f₂ s₁ _ _ (impure (s₂ , _)) _ with s₁ ≟ s₂
|⟨s⟩f₁|∧|[s]f₂|→⟨s⟩f₁∧f₂ s₁ _ _ (impure (s₂ , _)) () | no _
|⟨s⟩f₁|∧|[s]f₂|→⟨s⟩f₁∧f₂ s _ _ (impure (.s , _)) ((p , h₁) , h∀₂) | yes refl = p , h₁ , h∀₂ p

-- Theorems for [_]_

~|[s]f|⇔⟨s⟩~f : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f : Formula C) → (x : C ⋆ α) → ~ ([ s ] f) ⊩ x ⇔ ⟨ s ⟩ ~ f ⊩ x
to (~|[s]f|⇔⟨s⟩~f _ _ (pure _)) h¬∀ = lift (h¬∀ tt)
to (~|[s]f|⇔⟨s⟩~f s₁ f x@(impure (s₂ , c))) h¬∀ with ⊩-dec (⟨ s₁ ⟩ ~ f) x
... | yes h∃ = h∃
... | no h¬∃ with s₁ ≟ s₂
...   | no _ = lift (h¬∀ tt)
...   | yes refl = ⊥-elim₀ (h¬∀ λ p → case ⊩-dec f (c p) of λ { (yes h) → h ; (no ¬h) → ⊥-elim₀ (h¬∃ (p , ¬h)) })
from (~|[s]f|⇔⟨s⟩~f s₁ _ (impure (s₂ , _))) h∃ _ with s₁ ≟ s₂
... | no _ = ⊥-elim h∃
from (~|[s]f|⇔⟨s⟩~f s _ (impure (.s , _))) (p , ¬h) h∀ | yes refl = ¬h (h∀ p)

[s]true⇔true : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (x : C ⋆ α) → [ s ] true ⊩ x ⇔ true ⊩ x
to ([s]true⇔true _ _) _ = tt
from ([s]true⇔true _ (pure _)) _ = tt
from ([s]true⇔true s₁ (impure (s₂ , _))) _ with s₁ ≟ s₂
... | no _ = tt
... | yes refl = const tt

[s]f₁∧f₂⇔|[s]f₁|∧|[s]f₂| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → [ s ] f₁ ∧ f₂ ⊩ x ⇔ ([ s ] f₁) ∧ ([ s ] f₂) ⊩ x
to ([s]f₁∧f₂⇔|[s]f₁|∧|[s]f₂| _ _ _ (pure _)) _ = tt , tt
to ([s]f₁∧f₂⇔|[s]f₁|∧|[s]f₂| s₁ _ _ (impure (s₂ , _))) h∀ with s₁ ≟ s₂
... | no _ = tt , tt
... | yes refl = (proj₁ ∘ h∀) , (proj₂ ∘ h∀)
from ([s]f₁∧f₂⇔|[s]f₁|∧|[s]f₂| _ _ _ (pure _)) _ = tt
from ([s]f₁∧f₂⇔|[s]f₁|∧|[s]f₂| s₁ _ _ (impure (s₂ , _))) _ with s₁ ≟ s₂
... | no _ = tt
from ([s]f₁∧f₂⇔|[s]f₁|∧|[s]f₂| s _ _ (impure (.s , _))) (h∀₁ , h∀₂) | yes refl = λ p → h∀₁ p , h∀₂ p

[s]f₁∨f₂→|⟨s⟩f₁|∨|[s]f₂| : ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → (s : Shape C) → (f₁ f₂ : Formula C) → (x : C ⋆ α) → [ s ] f₁ ∨ f₂ ⊩ x → (⟨ s ⟩ f₁) ∨ ([ s ] f₂) ⊩ x
[s]f₁∨f₂→|⟨s⟩f₁|∨|[s]f₂| _ _ _ (pure _) _ = inj₂ tt
[s]f₁∨f₂→|⟨s⟩f₁|∨|[s]f₂| s₁ f₁ f₂ x@(impure (s₂ , _)) h with ⊩-dec (⟨ s₁ ⟩ f₁) x
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊩-dec ([ s₁ ] f₂) x
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with s₁ ≟ s₂
...     | no _ = inj₂ tt
...     | yes _ = ⊥-elim₀ (h¬∀ λ p → case h p of λ { (inj₁ h₁) → ⊥-elim₀ (h¬∃ (p , h₁)) ; (inj₂ h₂) → h₂ })
