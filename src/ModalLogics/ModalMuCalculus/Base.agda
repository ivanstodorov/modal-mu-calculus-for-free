module ModalLogics.ModalMuCalculus.Base where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Empty.Polymorphic using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃-syntax)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (¬_; yes; no; _because_; Dec)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

open Effect
open Dec ⦃...⦄
open IsDecEquivalence ⦃...⦄

data Formula (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula ε
  ~_ : Formula ε → Formula ε
  _∧_ _∨_ _⇒_ : Formula ε → Formula ε → Formula ε
  ⟨_⟩_ [_]_ : C ε → Formula ε → Formula ε
  μ_．_ ν_．_ : String → Formula ε → Formula ε
  var : String → Formula ε

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_
infix 30 μ_．_
infix 30 ν_．_

_⊢_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → Formula ε → Free ε α → Set ℓ₂
f ⊢ x = helper [] f x
  where
  helper : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → List String → Formula ε → Free ε α → Set ℓ₂
  helper _ true _ = ⊤
  helper _ false _ = ⊥
  helper vs (~ f) x = ¬ helper vs f x
  helper vs (f₁ ∧ f₂) x = helper vs f₁ x × helper vs f₂ x
  helper vs (f₁ ∨ f₂) x = helper vs f₁ x ⊎ helper vs f₂ x
  helper vs (f₁ ⇒ f₂) x = helper vs f₁ x → helper vs f₂ x
  helper _ (⟨ _ ⟩ _) (pure _) = ⊥
  helper vs (⟨ c₁ ⟩ f) (step c₂ k) with c₁ ≟ c₂
  ... | no _ = ⊥
  ... | yes _ = ∃[ r ] helper vs f (k r)
  helper vs ([ _ ] _) (pure _) = ⊤
  helper vs ([ c₁ ] f) (step c₂ k) with c₁ ≟ c₂
  ... | no _ = ⊤
  ... | yes _ = ∀ r → helper vs f (k r)
  helper vs (μ v ． f) x = {!   !}
  helper vs (ν v ． f) x = {!   !}
  helper vs (var v) x = {!   !}

infix 25 _⊢_

postulate
  ⊢-dec : {ε : Effect ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → (f : Formula ε) → (x : Free ε α) → Dec (f ⊢ x)

_⊢_!_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula ε → program ε I O → I → Set ℓ₂
f ⊢ x ! i = f ⊢ (x i)

infix 25 _⊢_!_

⊢-decP : {ε : Effect ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula ε) → (x : program ε I O) → (i : I) → Dec (f ⊢ x ! i)
does ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | does because _ = does
proof ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | _ because proof = proof

_▸_⊢_!_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula ε → recursiveProgram ε I O → I → Set ℓ₂
n ▸ f ⊢ x ! i = f ⊢ (recursionHandler x n) i

infix 25 _▸_⊢_!_

⊢-decR : {ε : Effect ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (f : Formula ε) → (x : recursiveProgram ε I O) → (i : I) → Dec (n ▸ f ⊢ x ! i)
does ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | _ because proof = proof
