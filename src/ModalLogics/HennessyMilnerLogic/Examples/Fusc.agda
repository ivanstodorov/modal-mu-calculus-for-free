{-# OPTIONS --overlapping-instances #-}
module ModalLogics.HennessyMilnerLogic.Examples.Fusc where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (const)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Effect
open Eq ⦃...⦄

emptyEffect : Effect {_} {0ℓ}
C emptyEffect = ⊥
R emptyEffect ()

instance
  emptyEffectEq : Eq (C emptyEffect)
  _==_ ⦃ emptyEffectEq ⦄ ()

fusc : recursiveProgram emptyEffect ℕ (const ℕ)
fusc zero = pure zero
fusc (suc n) = do
  fn ← callF n
  ffn ← callF fn
  pure (suc ffn)

test : (recursionHandler fusc 3) 3 ≡ pure (just 3)
test = refl
