module ModalLogics.HennessyMilnerLogic.Examples.Authentication where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Bool using (Bool; if_then_else_)
open import Data.Empty using (⊥) renaming (⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤) renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Function.Base using (const; id)
open import Level using (lift)
open import ModalLogics.HennessyMilnerLogic.Base
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; _≢_)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ)

open Eq ⦃...⦄ public

data AuthOperations : Set where
  login : ℕ → AuthOperations
  logout : AuthOperations

authEffect : Effect
Effect.C authEffect = AuthOperations
Effect.R authEffect (login _) = Bool
Effect.R authEffect logout = ⊤

instance
  authEffectEq : Eq (Effect.C authEffect)
  does (_==_ ⦃ authEffectEq ⦄ (login n₁) (login n₂)) with n₁ ≟ n₂
  ... | no _ = Bool.false
  ... | yes _ = Bool.true
  proof (_==_ ⦃ authEffectEq ⦄ (login n₁) (login n₂)) with n₁ ≟ n₂
  ... | no ¬p = ofⁿ λ {refl → ¬p refl}
  ... | yes refl = ofʸ refl
  does (_==_ ⦃ authEffectEq ⦄ (login _) logout) = Bool.false
  proof (_==_ ⦃ authEffectEq ⦄ (login _) logout) = ofⁿ λ ()
  does (_==_ ⦃ authEffectEq ⦄ logout (login _)) = Bool.false
  proof ((_==_ ⦃ authEffectEq ⦄ logout (login _))) = ofⁿ λ ()
  does (_==_ ⦃ authEffectEq ⦄ logout logout) = Bool.true
  proof (_==_ ⦃ authEffectEq ⦄ logout logout) = ofʸ refl

exceptionEffect : Effect
Effect.C exceptionEffect = ⊤
Effect.R exceptionEffect _ = ⊥

instance
  exceptionEffectEq : Eq (Effect.C exceptionEffect)
  does (_==_ ⦃ exceptionEffectEq ⦄ tt tt) = Bool.true
  proof (_==_ ⦃ exceptionEffectEq ⦄ tt tt) = ofʸ refl

testProgram : program (authEffect :+: exceptionEffect) ℕ (const ⊤)
testProgram n = do
  lift b ← step (inj₁ (login n)) pure
  ( if b
    then step (inj₁ logout) (λ (lift h) → pure h)
    else step (inj₂ tt₀) (λ (lift h) → ⊥-elim₀ h) )

property₁ : Formula (authEffect :+: exceptionEffect)
property₁ = [ inj₁ logout ] false

test₁ : property₁ ⊢ testProgram ! 0
test₁ = tt

property₂ : Formula (authEffect :+: exceptionEffect)
property₂ = ⟨ inj₁ (login 0) ⟩ ⟨ inj₁ logout ⟩ true

test₂ : property₂ ⊢ testProgram ! 0
test₂ = lift Bool.true , tt , tt

property₃ : Formula (authEffect :+: exceptionEffect)
property₃ = ⟨ inj₁ (login 0) ⟩ [ inj₁ (login 0) ] true

test₃ : property₃ ⊢ testProgram ! 0
test₃ = lift Bool.false , tt

property₄ : Formula (authEffect :+: exceptionEffect)
property₄ = ⟨ inj₁ (login 0) ⟩ [ inj₁ logout ] false

test₄ : property₄ ⊢ testProgram ! 0
test₄ = lift Bool.false , tt

property₅ : Formula (authEffect :+: exceptionEffect)
property₅ = [ inj₁ (login 0) ] [ inj₂ tt₀ ] false

test₅ : property₅ ⊢ testProgram ! 0
test₅ (lift Bool.false) = ⊥-elim
test₅ (lift Bool.true) = tt

property₆ : Formula (authEffect :+: exceptionEffect)
property₆ = [ inj₁ (login 0) ] [ inj₂ tt₀ ] true

test₆ : property₆ ⊢ testProgram ! 0
test₆ (lift Bool.false) = ⊥-elim
test₆ (lift Bool.true) = tt

property₇ : (n : ℕ) → Formula (authEffect :+: exceptionEffect)
property₇ n = [ inj₁ (login n) ] false

test₇ : ∀ (n : ℕ) → n ≢ 0 → property₇ n ⊢ testProgram ! 0
test₇ zero h = ⊥-elim₀ (h refl)
test₇ (suc _) h = tt

property₈ : (c : Effect.C (authEffect :+: exceptionEffect)) → Formula (authEffect :+: exceptionEffect)
property₈ c = ⟨ inj₁ (login 0) ⟩ (([ c ] true) ∧ ([ c ] false))

test₈ : ∀ c → property₈ c ⊢ testProgram ! 0
test₈ (inj₁ _) = lift Bool.false , tt , tt
test₈ (inj₂ _) = lift Bool.false , (const tt) , ⊥-elim
