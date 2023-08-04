module Examples.Authentication where

open import Common.Effect
open import Common.Free
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Function.Base using (id)
open import ModalLogics.HennessyMilnerLogic
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data AuthOperations : Set where
  login : ℕ → AuthOperations
  logout : AuthOperations

AuthEffect : Effect
Effect.C AuthEffect = AuthOperations
Effect.R AuthEffect (login x) = Bool
Effect.R AuthEffect logout = ⊤

instance
  DecideAuth : Decide AuthEffect
  Decide._≟_ DecideAuth (login l) (login r) = l ≡ᵇ r
  Decide._≟_ DecideAuth (login _) logout = false
  Decide._≟_ DecideAuth logout (login _) = false
  Decide._≟_ DecideAuth logout logout = true

ExceptionEffect : Effect
Effect.C ExceptionEffect = ⊤
Effect.R ExceptionEffect _ = ⊥

instance
  DecideException : Decide ExceptionEffect
  Decide._≟_ DecideException _ _ = true

program : Free (AuthEffect ⊕ ExceptionEffect) ⊤
program = do
  b ← Step (inj₁ (login 0)) Pure
  ( if b
    then Step (inj₁ logout) Pure
    else Step (inj₂ tt) (λ _ → Pure tt) )

property₁ : Formula (AuthEffect ⊕ ExceptionEffect)
property₁ = [ inj₁ logout ] false

test₁ : program ⊢ property₁
test₁ = tt

property₂ : Formula (AuthEffect ⊕ ExceptionEffect)
property₂ = ⟨ inj₁ (login 0) ⟩ ⟨ inj₁ logout ⟩ true

test₂ : program ⊢ property₂
test₂ = Bool.true , tt , tt

property₃ : Formula (AuthEffect ⊕ ExceptionEffect)
property₃ = ⟨ inj₁ (login 0) ⟩ [ inj₁ (login 0) ] true

test₃ : program ⊢ property₃
test₃ = Bool.false , tt

property₄ : Formula (AuthEffect ⊕ ExceptionEffect)
property₄ = ⟨ inj₁ (login 0) ⟩ [ inj₁ logout ] false

test₄ : program ⊢ property₄
test₄ = Bool.false , tt

property₅ : Formula (AuthEffect ⊕ ExceptionEffect)
property₅ = [ inj₁ (login 0) ] [ inj₂ tt ] false

test₅ : program ⊢ property₅
test₅ = helper
  where
    helper : _
    helper false = id
    helper true = tt

property₆ : Formula (AuthEffect ⊕ ExceptionEffect)
property₆ = [ inj₁ (login 0) ] [ inj₂ tt ] true

test₆ : program ⊢ property₆
test₆ = helper
  where
    helper : _
    helper false = ⊥-elim
    helper true = tt

property₇ : (n : ℕ) → Formula (AuthEffect ⊕ ExceptionEffect)
property₇ n = [ inj₁ (login n) ] false

test₇ : ∀ (n : ℕ) → n ≢ 0 → program ⊢ property₇ n
test₇ zero h = ⊥-elim (h _≡_.refl)
test₇ (suc n) h = tt
