{-# OPTIONS --without-K --safe --guardedness #-}
module Common.FixedPoints where

open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; fromℕ<)
open import Data.List using (lookup)
open import Data.List.NonEmpty using (List⁺; length; toList)
open import Data.Nat using (ℕ; _<?_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; suc)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (IUniversal; _⇒_)

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

data Maybe' (α : Set ℓ) : Set ℓ where
  val : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

record IndexedContainer (I : Set ℓ) : Set (suc ℓ) where
  constructor _▷_
  field
    Shape : ℕ
    Position : Fin (Shape) → I → Maybe' (I × ℕ) → Set ℓ

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

⟦_⟧ᵢ : {I : Set ℓ} → (xs : List⁺ (FixedPoint × IndexedContainer I)) → (Maybe' (I × ℕ) → Set ℓ) → (Maybe' (I × ℕ) → Set ℓ) → Maybe' (I × ℕ) → Set ℓ
⟦ xs ⟧ᵢ w m (val (i , n)) with n <? length xs
... | no _ = ⊥
... | yes h with fromℕ< h
...   | n with lookup (toList xs) n
...     | leastFP , (S ▷ P) = Σ[ s ∈ Fin S ] ∀[ P s i ⇒ w ]
...     | greatestFP , (S ▷ P) = Σ[ s ∈ Fin S ] ∀[ P s i ⇒ m ]
⟦ _ ⟧ᵢ _ _ done = ⊤
⟦ _ ⟧ᵢ _ _ fail = ⊥

record WI {I : Set ℓ} (_ : List⁺ (FixedPoint × IndexedContainer I)) (_ : Maybe' (I × ℕ)) : Set ℓ
record MI {I : Set ℓ} (_ : List⁺ (FixedPoint × IndexedContainer I)) (_ : Maybe' (I × ℕ)) : Set ℓ

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
