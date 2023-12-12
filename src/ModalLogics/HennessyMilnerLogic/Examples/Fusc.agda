module ModalLogics.HennessyMilnerLogic.Examples.Fusc where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁)
open import Function.Base using (const)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

fusc : recursiveProgram emptyEffect ℕ (const ℕ)
fusc zero = pure zero
fusc (suc n) = do
  fn ← step (inj₁ (call n)) pure
  ffn ← step (inj₁ (call fn)) pure
  pure (suc ffn)

test : (recursionHandler fusc 3) 3 ≡ pure (just 3)
test = refl
