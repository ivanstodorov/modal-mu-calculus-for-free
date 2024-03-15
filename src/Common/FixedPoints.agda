{-# OPTIONS --without-K --safe --guardedness #-}
module Common.FixedPoints where

open import Data.Container using (Container)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin)
open import Data.List.NonEmpty using (List⁺; foldr)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; lookup)
open import Function using (_∘_; case_of_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Container

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- {-# NO_POSITIVITY_CHECK #-}
-- data Mu {c : Container zero zero} {α : Set} (F : (Free c α → Set) → Free c α → Set) : Free c α → Set where
--   In : ∀[ F (Mu F) ⇒ Mu F ]

-- {-# NO_POSITIVITY_CHECK #-}
-- record Nu {c : Container zero zero} {α : Set} (F : (Free c α → Set) → Free c α → Set) (x : Free c α) : Set where
--   coinductive
--   constructor Ni
--   field
--     Ni : F (Nu F) x

data Maybe' (α : Set ℓ) : Set ℓ where
  val : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

data Result (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  val : Maybe' ((C ⋆ α) × Fin n) → Result C α n
  exists : (s : Shape C) → (Position C s → Result C α n) → Result C α n
  all : (s : Shape C) → (Position C s → Result C α n) → Result C α n

record IndexedContainer (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shapeᵢ : ℕ
    Positionᵢ : Fin (Shapeᵢ) → C ⋆ α → List⁺ (Result C α n)

open IndexedContainer

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

⟦_⟧ᵢ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → (xs : Vec (FixedPoint × IndexedContainer C α (suc n)) (suc n)) → (Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
⟦ xs ⟧ᵢ w m (val (i , n)) = case lookup xs n of λ { (leastFP , (S ▷ P)) → Σ[ s ∈ Fin S ] ∀ {x} → foldr (_⊎_ ∘ (unfold x)) (unfold x) (P s i) → w x ; (greatestFP , (S ▷ P)) → Σ[ s ∈ Fin S ] ∀ {x} → foldr (_⊎_ ∘ (unfold x)) (unfold x) (P s i) → m x }
  where
  unfold : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Maybe' ((C ⋆ α) × Fin n) → Result C α n → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  unfold x (val v) = x ≡ v
  unfold {C = C} x (exists s f) = Σ[ p ∈ Position C s ] unfold x (f p)
  unfold {C = C} x (all s f) = ∀ (p : Position C s) → unfold x (f p)
⟦ _ ⟧ᵢ _ _ done = ⊤
⟦ _ ⟧ᵢ _ _ fail = ⊥

record WI {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × IndexedContainer C α (suc n)) (suc n)) (_ : Maybe' ((C ⋆ α) × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record MI {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × IndexedContainer C α (suc n)) (suc n)) (_ : Maybe' ((C ⋆ α) × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record WI xs n where
  inductive
  constructor wi
  field
    In : ⟦ xs ⟧ᵢ (WI xs) (MI xs) n

record MI xs n where
  coinductive
  constructor mi
  field
    Ni : ⟦ xs ⟧ᵢ (WI xs) (MI xs) n
