{-# OPTIONS --without-K --safe --guardedness #-}
module Common.FixedPoints where

open import Common.Utils using (Maybe')
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (fromℕ<)
open import Data.List using (List; lookup)
open import Data.List.NonEmpty using (List⁺; _∷_; length; toList)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _<?_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; suc; _⊔_)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (IUniversal; _⇒_)

open Maybe'
open Maybe

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

record IndexedContainer (I : Set ℓ₁) (ℓ₂ ℓ₃ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  constructor _▷_
  field
    Shape : I → Set ℓ₁
    Position : (i : I) → Shape i → Maybe' (I × Maybe ℕ) → Set ℓ₂

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

⟦_⟧ᵢ : {I : Set ℓ₁} → (xs : List⁺ (FixedPoint × IndexedContainer I ℓ₂ ℓ₃)) → (Maybe' (I × Maybe ℕ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' (I × Maybe ℕ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Maybe' (I × Maybe ℕ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
⟦ xs ⟧ᵢ w m (val (i , just n)) with ℕ.suc n <? length xs
... | no _ = ⊥
... | yes h with fromℕ< h
...   | n with lookup (toList xs) n
...     | leastFP , (S ▷ P) = Σ[ s ∈ S i ] ∀[ P i s ⇒ w ]
...     | greatestFP , (S ▷ P) = Σ[ s ∈ S i ] ∀[ P i s ⇒ m ]
⟦ (leastFP , (S ▷ P)) ∷ _ ⟧ᵢ w _ (val (i , nothing)) = Σ[ s ∈ S i ] ∀[ P i s ⇒ w ]
⟦ (greatestFP , (S ▷ P)) ∷ _ ⟧ᵢ _ m (val (i , nothing)) = Σ[ s ∈ S i ] ∀[ P i s ⇒ m ]
⟦ _ ⟧ᵢ _ _ done = ⊤
⟦ _ ⟧ᵢ _ _ fail = ⊥

-- data WI' {I : Set ℓ₁} (xs : List⁺ (FixedPoint × IndexedContainer I ℓ₂ ℓ₃)) : Maybe' (I × Maybe ℕ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record WI' {I : Set ℓ₁} (_ : List⁺ (FixedPoint × IndexedContainer I ℓ₂ ℓ₃)) (_ : Maybe' (I × Maybe ℕ)) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record MI' {I : Set ℓ₁} (_ : List⁺ (FixedPoint × IndexedContainer I ℓ₂ ℓ₃)) (_ : Maybe' (I × Maybe ℕ)) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

-- data WI' xs where
--   In : ∀[ ⟦ xs ⟧ᵢ (WI' xs) (MI' xs) ⇒ WI' xs ]

record WI' xs n where
  inductive
  constructor In
  field
    In : ⟦ xs ⟧ᵢ (WI' xs) (MI' xs) n

record MI' xs n where
  coinductive
  constructor Ni
  field
    Ni : ⟦ xs ⟧ᵢ (WI' xs) (MI' xs) n

WI : {I : Set ℓ₁} → IndexedContainer I ℓ₂ ℓ₃ → List (FixedPoint × IndexedContainer I ℓ₂ ℓ₃) → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
WI x xs i = WI' ((leastFP , x) ∷ xs) (val (i , nothing))

MI : {I : Set ℓ₁} → IndexedContainer I ℓ₂ ℓ₃ → List (FixedPoint × IndexedContainer I ℓ₂ ℓ₃) → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
MI x xs i = MI' ((greatestFP , x) ∷ xs) (val (i , nothing))
