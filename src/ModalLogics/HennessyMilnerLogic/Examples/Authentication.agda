{-# OPTIONS --without-K --safe --overlapping-instances #-}
module ModalLogics.HennessyMilnerLogic.Examples.Authentication where

open import Common.Container using (_:+:_; _:<:_)
open import Common.Program using (Program)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Container using (Container)
open import Data.Container.FreeMonad using (_⋆_; _>>=_)
open import Data.Empty using (⊥) renaming (⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤) renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_∘_; const)
open import Level using (Level; 0ℓ; lift)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_!_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ)

open _:<:_
open Bool
open Container
open _⋆_
open ℕ
open Formula
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl; _≟_)

private variable
  ℓ₁ ℓ₂ ℓ₃ : Level

data AuthOperations : Set where
  login : ℕ → AuthOperations
  logout : AuthOperations

authEffect : Container 0ℓ 0ℓ
Shape authEffect = AuthOperations
Position authEffect (login _) = Bool
Position authEffect logout = ⊤

instance
  authEffectEqIsDecEq : IsDecEquivalence {A = Shape authEffect} _≡_
  authEffectEqIsDecEq = isDecEquivalence authEffectEqDec
    where
    authEffectEqDec : Decidable {A = Shape authEffect} _≡_
    does (authEffectEqDec (login n₁) (login n₂)) with n₁ ≟ n₂
    ... | no _ = false
    ... | yes _ = true
    does (authEffectEqDec (login _) logout) = false
    does (authEffectEqDec logout (login _)) = false
    does (authEffectEqDec logout logout) = true
    proof (authEffectEqDec (login n₁) (login n₂)) with n₁ ≟ n₂
    ... | no ¬p = ofⁿ λ { refl → ¬p refl }
    ... | yes refl = ofʸ refl
    proof (authEffectEqDec (login _) logout) = ofⁿ λ ()
    proof (authEffectEqDec logout (login _)) = ofⁿ λ ()
    proof (authEffectEqDec logout logout) = ofʸ refl

loginS : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → ℕ → Shape C
loginS _ ⦃ inst ⦄ = (injS inst) ∘ login

loginF : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → ℕ → C ⋆ Bool
loginF C ⦃ inst ⦄ n = impure (loginS C n , pure ∘ projP inst)

logoutS : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → Shape C
logoutS _ ⦃ inst ⦄ = injS inst logout

logoutF : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → C ⋆ ⊤
logoutF C ⦃ inst ⦄ = impure (logoutS C , pure ∘ projP inst)

exceptionEffect : Container 0ℓ 0ℓ
Shape exceptionEffect = ⊤
Position exceptionEffect _ = ⊥

instance
  exceptionEffectEqIsDecEq : IsDecEquivalence {A = Shape exceptionEffect} _≡_
  exceptionEffectEqIsDecEq = isDecEquivalence exceptionEffectEqDec
    where
    exceptionEffectEqDec : Decidable {A = Shape exceptionEffect} _≡_
    does (exceptionEffectEqDec tt₀ tt₀) = true
    proof (exceptionEffectEqDec tt₀ tt₀) = ofʸ refl

exceptionS : (C : Container ℓ₁ ℓ₂) → ⦃ exceptionEffect :<: C ⦄ → Shape C
exceptionS _ ⦃ inst ⦄ = injS inst tt₀

exceptionF : (C : Container ℓ₁ ℓ₂) → ⦃ exceptionEffect :<: C ⦄ → {α : Set ℓ₃} → C ⋆ α
exceptionF C ⦃ inst ⦄ = impure (exceptionS C , ⊥-elim₀ ∘ projP inst)

e : Container 0ℓ 0ℓ
e = authEffect :+: exceptionEffect

testProgram : Program e ℕ (const ⊤)
testProgram n = do
  b ← loginF e n
  ( if b
    then logoutF e
    else exceptionF e )

property₁ : Formula e
property₁ = [ logoutS e ] false

test₁ : property₁ ⊩ testProgram ! 0
test₁ = tt

property₂ : Formula e
property₂ = ⟨ loginS e 0 ⟩ ⟨ logoutS e ⟩ true

test₂ : property₂ ⊩ testProgram ! 0
test₂ = lift Bool.true , tt , tt

property₃ : Formula e
property₃ = ⟨ loginS e 0 ⟩ [ loginS e 0 ] true

test₃ : property₃ ⊩ testProgram ! 0
test₃ = lift Bool.false , tt

property₄ : Formula e
property₄ = ⟨ loginS e 0 ⟩ [ logoutS e ] false

test₄ : property₄ ⊩ testProgram ! 0
test₄ = lift Bool.false , tt

property₅ : Formula e
property₅ = [ loginS e 0 ] [ exceptionS e ] false

test₅ : property₅ ⊩ testProgram ! 0
test₅ (lift Bool.false) = ⊥-elim
test₅ (lift Bool.true) = tt

property₆ : Formula e
property₆ = [ loginS e 0 ] [ exceptionS e ] true

test₆ : property₆ ⊩ testProgram ! 0
test₆ (lift Bool.false) = ⊥-elim
test₆ (lift Bool.true) = tt

property₇ : ℕ → Formula e
property₇ n = [ loginS e n ] false

test₇ : ∀ (n : ℕ) → n ≢ 0 → property₇ n ⊩ testProgram ! 0
test₇ zero h = ⊥-elim₀ (h refl)
test₇ (suc _) h = tt

property₈ : Shape e → Formula e
property₈ c = ⟨ loginS e 0 ⟩ ([ c ] true) ∧ ([ c ] false)

test₈ : ∀ c → property₈ c ⊩ testProgram ! 0
test₈ (inj₁ _) = lift Bool.false , tt , tt
test₈ (inj₂ _) = lift Bool.false , (const tt) , ⊥-elim
