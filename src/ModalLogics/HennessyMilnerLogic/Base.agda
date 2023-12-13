module ModalLogics.HennessyMilnerLogic.Base where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)
open import Relation.Nullary using (¬_; yes; no; _because_; Dec)

open Effect
open Eq ⦃...⦄
open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Formula (ε : Effect {ℓ₁} {ℓ₂}) : Set ℓ₁ where
  true false : Formula ε
  ~_ : Formula ε → Formula ε
  _∧_ _∨_ _⇒_ : Formula ε → Formula ε → Formula ε
  ⟨_⟩_ [_]_ : C ε → Formula ε → Formula ε

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_

_⊢_ : {ε : Effect {ℓ₁} {ℓ₂}} → ⦃ Eq (C ε) ⦄ → {α : Set ℓ₃} → Formula ε → Free ε α → Set ℓ₂
true ⊢ x = ⊤
false ⊢ x = ⊥
(~ f) ⊢ x = ¬ (f ⊢ x)
(f₁ ∧ f₂) ⊢ x = f₁ ⊢ x × f₂ ⊢ x
(f₁ ∨ f₂) ⊢ x = f₁ ⊢ x ⊎ f₂ ⊢ x
(f₁ ⇒ f₂) ⊢ x = f₁ ⊢ x → f₂ ⊢ x
(⟨ _ ⟩ _) ⊢ pure _ = ⊥
(⟨ c₁ ⟩ f) ⊢ step c₂ k with c₁ == c₂
... | no _ = ⊥
... | yes _ = ∃[ r ] f ⊢ k r
([ _ ] _) ⊢ pure _ = ⊤
([ c₁ ] f) ⊢ step c₂ k with c₁ == c₂
... | no _ = ⊤
... | yes _ = ∀ r → f ⊢ k r

infix 25 _⊢_

postulate
  ⊢-dec : {ε : Effect {ℓ₁} {ℓ₂}} → ⦃ _ : Eq (C ε) ⦄ → {α : Set ℓ₃} → (f : Formula ε) → (x : Free ε α) → Dec (f ⊢ x)

_⊢_!_ : {ε : Effect {ℓ₁} {ℓ₂}} → ⦃ Eq (C ε) ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula ε → program ε I O → I → Set ℓ₂
f ⊢ x ! i = f ⊢ (x i)

infix 25 _⊢_!_

⊢-decP : {ε : Effect {ℓ₁} {ℓ₂}} → ⦃ _ : Eq (C ε) ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula ε) → (x : program ε I O) → (i : I) → Dec (f ⊢ x ! i)
does ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | does because _ = does
proof ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | _ because proof = proof

_▸_⊢_!_ : {ε : Effect {ℓ₁} {ℓ₂}} → ⦃ Eq (C ε) ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula ε → recursiveProgram ε I O → I → Set ℓ₂
n ▸ f ⊢ x ! i = f ⊢ (recursionHandler x n) i

infix 25 _▸_⊢_!_

⊢-decR : {ε : Effect {ℓ₁} {ℓ₂}} → ⦃ _ : Eq (C ε) ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (f : Formula ε) → (x : recursiveProgram ε I O) → (i : I) → Dec (n ▸ f ⊢ x ! i)
does ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | _ because proof = proof
