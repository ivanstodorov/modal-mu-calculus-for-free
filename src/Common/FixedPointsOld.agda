{-# OPTIONS --without-K --safe --guardedness #-}
module Common.FixedPointsOld where

open import Data.Container using () renaming (Container to Containerˢᵗᵈ)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin)
open import Data.List.NonEmpty using (List⁺; foldr)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; lookup)
open import Function using (_∘_; case_of_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Containerˢᵗᵈ

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

infix 30 val_

data Maybe' (α : Set ℓ) : Set ℓ where
  val_ : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

infix 25 ∃〔_〕_
infix 25 ∀〔_〕_

data Result (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  val_ : Maybe' ((C ⋆ α) × Fin n) → Result C α n
  ∃〔_〕_ : (s : Shape C) → (Position C s → Result C α n) → Result C α n
  ∀〔_〕_ : (s : Shape C) → (Position C s → Result C α n) → Result C α n

record Container (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shape : ℕ
    Position : Fin Shape → C ⋆ α → List⁺ (Result C α n)

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

extend : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → (xs : Vec (FixedPoint × Container C α (suc n)) (suc n)) → (Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
extend xs w m (val (i , n)) = case lookup xs n of λ { (leastFP , (_ ▷ P)) → ∃[ s ] ∀ {x} → foldr (_⊎_ ∘ (unfold x)) (unfold x) (P s i) → w x ; (greatestFP , (_ ▷ P)) → ∃[ s ] ∀ {x} → foldr (_⊎_ ∘ (unfold x)) (unfold x) (P s i) → m x }
  where
  unfold : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Maybe' ((C ⋆ α) × Fin n) → Result C α n → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  unfold x (val v) = x ≡ v
  unfold x (∃〔 _ 〕 f) = ∃[ p ] unfold x (f p)
  unfold x (∀〔 _ 〕 f) = ∀ p → unfold x (f p)
extend _ _ _ done = ⊤
extend _ _ _ fail = ⊥

record W {C : Containerˢᵗᵈ ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × Container C α (suc n)) (suc n)) (_ : Maybe' ((C ⋆ α) × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record M {C : Containerˢᵗᵈ ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × Container C α (suc n)) (suc n)) (_ : Maybe' ((C ⋆ α) × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record W xs n where
  inductive
  constructor wᶜ
  field
    In : extend xs (W xs) (M xs) n

record M xs n where
  coinductive
  constructor mᶜ
  field
    Ni : extend xs (W xs) (M xs) n
