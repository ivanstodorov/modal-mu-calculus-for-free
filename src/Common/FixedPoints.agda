{-# OPTIONS --without-K --safe --guardedness #-}
module Common.FixedPoints where

open import Common.Utils using (Maybe')
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; fromℕ<)
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
  ℓ : Level

-- {-# NO_POSITIVITY_CHECK #-}
-- data Mu {c : Container zero zero} {α : Set} (F : (Free c α → Set) → Free c α → Set) : Free c α → Set where
--   In : ∀[ F (Mu F) ⇒ Mu F ]

-- {-# NO_POSITIVITY_CHECK #-}
-- record Nu {c : Container zero zero} {α : Set} (F : (Free c α → Set) → Free c α → Set) (x : Free c α) : Set where
--   coinductive
--   constructor Ni
--   field
--     Ni : F (Nu F) x

record IndexedContainer (I : Set ℓ) : Set (suc ℓ) where
  constructor _▷_
  field
    Shape : ℕ
    Position : Fin (Shape) → I → Maybe' (I × Maybe ℕ) → Set ℓ

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

⟦_⟧ᵢ : {I : Set ℓ} → (xs : List⁺ (FixedPoint × IndexedContainer I)) → (Maybe' (I × Maybe ℕ) → Set ℓ) → (Maybe' (I × Maybe ℕ) → Set ℓ) → Maybe' (I × Maybe ℕ) → Set ℓ
⟦ xs ⟧ᵢ w m (val (i , just n)) with ℕ.suc n <? length xs
... | no _ = ⊥
... | yes h with fromℕ< h
...   | n with lookup (toList xs) n
...     | leastFP , (S ▷ P) = Σ[ s ∈ Fin S ] ∀[ P s i ⇒ w ]
...     | greatestFP , (S ▷ P) = Σ[ s ∈ Fin S ] ∀[ P s i ⇒ m ]
⟦ (leastFP , (S ▷ P)) ∷ _ ⟧ᵢ w _ (val (i , nothing)) = Σ[ s ∈ Fin S ] ∀[ P s i ⇒ w ]
⟦ (greatestFP , (S ▷ P)) ∷ _ ⟧ᵢ _ m (val (i , nothing)) = Σ[ s ∈ Fin S ] ∀[ P s i ⇒ m ]
⟦ _ ⟧ᵢ _ _ done = ⊤
⟦ _ ⟧ᵢ _ _ fail = ⊥

record WI' {I : Set ℓ} (_ : List⁺ (FixedPoint × IndexedContainer I)) (_ : Maybe' (I × Maybe ℕ)) : Set ℓ
record MI' {I : Set ℓ} (_ : List⁺ (FixedPoint × IndexedContainer I)) (_ : Maybe' (I × Maybe ℕ)) : Set ℓ

record WI' xs n where
  inductive
  constructor wi
  field
    In : ⟦ xs ⟧ᵢ (WI' xs) (MI' xs) n

record MI' xs n where
  coinductive
  constructor mi
  field
    Ni : ⟦ xs ⟧ᵢ (WI' xs) (MI' xs) n

WI : {I : Set ℓ} → IndexedContainer I → List (FixedPoint × IndexedContainer I) → I → Set ℓ
WI x xs i = WI' ((leastFP , x) ∷ xs) (val (i , nothing))

MI : {I : Set ℓ} → IndexedContainer I → List (FixedPoint × IndexedContainer I) → I → Set ℓ
MI x xs i = MI' ((greatestFP , x) ∷ xs) (val (i , nothing))
