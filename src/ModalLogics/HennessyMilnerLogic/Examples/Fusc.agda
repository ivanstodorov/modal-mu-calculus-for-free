module ModalLogics.HennessyMilnerLogic.Examples.Fusc where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁)
open import Function.Base using (const)
open import Level using (0ℓ; lift)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

fusc : recursiveProgram (emptyEffect {0ℓ} {0ℓ}) ℕ (const ℕ)
fusc zero = pure zero
fusc (suc n) = do
  fn ← step (inj₁ (call n)) (λ (lift fn) → pure fn)
  ffn ← step (inj₁ (call fn)) (λ (lift ffn) → pure ffn)
  pure (suc ffn)

test : (recursionHandler fusc 3) 3 ≡ pure (just 3)
test = refl
