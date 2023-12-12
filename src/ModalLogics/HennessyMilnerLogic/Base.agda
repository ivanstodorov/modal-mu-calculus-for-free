module ModalLogics.HennessyMilnerLogic.Base where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_; yes; no; _because_; Dec)

open Eq ⦃...⦄
open Dec ⦃...⦄

data Formula (ε : Effect) : Set where
  true false : Formula ε
  ~_ : Formula ε → Formula ε
  _∧_ _∨_ _➔_ : Formula ε → Formula ε → Formula ε
  ⟨_⟩_ [_]_ : (Effect.C ε) → Formula ε → Formula ε

infix 25 true false
infix 30 ~_
infixl 40 _∧_
infixl 40 _∨_
infixl 40 _➔_
infixl 35 ⟨_⟩_
infixl 35 [_]_

_⊢_ : {ε : Effect} → ⦃ Eq (Effect.C ε) ⦄ → {α : Set} → Formula ε → Free ε α → Set
true ⊢ x = ⊤
false ⊢ x = ⊥
(~ f) ⊢ x = ¬ (f ⊢ x)
(f₁ ∧ f₂) ⊢ x = f₁ ⊢ x × f₂ ⊢ x
(f₁ ∨ f₂) ⊢ x = f₁ ⊢ x ⊎ f₂ ⊢ x
(f₁ ➔ f₂) ⊢ x = f₁ ⊢ x → f₂ ⊢ x
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
  ⊢-dec : {ε : Effect} → ⦃ _ : Eq (Effect.C ε) ⦄ → {α : Set} → (f : Formula ε) → (x : Free ε α) → Dec (f ⊢ x)

_⊢_!_ : {ε : Effect} → ⦃ Eq (Effect.C ε) ⦄ → {I : Set} → {O : I → Set} → Formula ε → program ε I O → I → Set
f ⊢ x ! i = f ⊢ (x i)

infix 25 _⊢_!_

⊢-decP : {ε : Effect} → ⦃ _ : Eq (Effect.C ε) ⦄ → {I : Set} → {O : I → Set} → (f : Formula ε) → (x : program ε I O) → (i : I) → Dec (f ⊢ x ! i)
does ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | does because _ = does
proof ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | _ because proof = proof

_▸_⊢_!_ : {ε : Effect} → ⦃ Eq (Effect.C ε) ⦄ → {I : Set} → {O : I → Set} → ℕ → Formula ε → recursiveProgram ε I O → I → Set
n ▸ f ⊢ x ! i = f ⊢ (recursionHandler x n) i

infix 25 _▸_⊢_!_

⊢-decR : {ε : Effect} → ⦃ _ : Eq (Effect.C ε) ⦄ → {I : Set} → {O : I → Set} → (n : ℕ) → (f : Formula ε) → (x : recursiveProgram ε I O) → (i : I) → Dec (n ▸ f ⊢ x ! i)
does ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | _ because proof = proof
  