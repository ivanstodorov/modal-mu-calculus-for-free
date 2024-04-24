{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.Programs.Effect where

open import Common.Injectable using (_:<:_)
open import Common.Program using (Program; ⦗_⦘; pure; impure)
open import Data.Bool using (Bool)
open import Data.Container using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Function using (_∘_; _∘₂_)
open import Level using (Level; 0ℓ)

open _:<:_
open Container

private variable
  ℓ₁ ℓ₂ ℓ₃ : Level

data InputShape : Set where
  input : InputShape

inputEffect : Container 0ℓ 0ℓ
Shape inputEffect = InputShape
Position inputEffect _ = String × ℕ

inputS : (C : Container ℓ₁ ℓ₂) → ⦃ inputEffect :<: C ⦄ → Shape C
inputS _ ⦃ inst ⦄ = injS inst input

inputP : {C : Container ℓ₁ ℓ₂} → ⦃ inputEffect :<: C ⦄ → Program C (String × ℕ)
inputP {C = C} ⦃ inst ⦄ = ⦗ impure (inputS C , λ p → ⦗ pure (projP inst p) ⦘) ⦘

data AuthShape : Set where
  login : String → ℕ → AuthShape
  logout : AuthShape

authEffect : Container 0ℓ 0ℓ
Shape authEffect = AuthShape
Position authEffect (login _ _) = Bool
Position authEffect logout = ⊤

loginS : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → String → ℕ → Shape C
loginS _ ⦃ inst ⦄ = injS inst ∘₂ login

loginP : {C : Container ℓ₁ ℓ₂} → ⦃ authEffect :<: C ⦄ → String → ℕ → Program C Bool
loginP {C = C} ⦃ inst ⦄ x n = ⦗ impure (loginS C x n , λ p → ⦗ pure (projP inst p) ⦘) ⦘

logoutS : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → Shape C
logoutS _ ⦃ inst ⦄ = injS inst logout

logoutP : {C : Container ℓ₁ ℓ₂} → ⦃ authEffect :<: C ⦄ → Program C ⊤
logoutP {C = C} ⦃ inst ⦄ = ⦗ impure (logoutS C , λ p → ⦗ pure (projP inst p) ⦘) ⦘

data ExceptionShape : Set where
  exception : ExceptionShape

exceptionEffect : Container 0ℓ 0ℓ
Shape exceptionEffect = ExceptionShape
Position exceptionEffect _ = ⊥

exceptionS : (C : Container ℓ₁ ℓ₂) → ⦃ exceptionEffect :<: C ⦄ → Shape C
exceptionS _ ⦃ inst ⦄ = injS inst exception

exceptionP : {C : Container ℓ₁ ℓ₂} → ⦃ exceptionEffect :<: C ⦄ → {α : Set ℓ₃} → Program C α
exceptionP {C = C} ⦃ inst ⦄ = ⦗ impure (exceptionS C , ⊥-elim ∘ projP inst) ⦘

effect : Container 0ℓ 0ℓ
effect = inputEffect ⊎ authEffect ⊎ exceptionEffect
