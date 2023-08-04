module ModalLogics.HennessyMilnerLogic where

open import Common.Effect
open import Common.Free
open import Data.Bool hiding (_∧_; _∨_; _≟_; _<_)
open import Data.Empty
open import Data.Nat hiding (_≟_; _<_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Nat.Induction
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Induction.WellFounded as WF
open import Level using (0ℓ)
open import Relation.Binary

open Decide ⦃ ... ⦄

data Formula (e : Effect) : Set where
  true false : Formula e
  ¬_ : Formula e → Formula e
  _∧_ _∨_ _➔_ : Formula e → Formula e → Formula e
  ⟨_⟩_ [_]_ : (Effect.C e) → Formula e → Formula e

-- ATTEMPT 1: Simple ⊢ function (doesn't work - termination checking failed)
-- _⊢_ : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → Formula e → Set
-- _ ⊢ true = ⊤
-- _ ⊢ false = ⊥
-- x ⊢ (¬ f) = x ⊢ (negate f)
--   where
--     negate : {e : Effect} → Formula e → Formula e
--     negate true = false
--     negate false = true
--     negate (¬ f) = f
--     negate (f₁ ∧ f₂) = (¬ f₁) ∨ (¬ f₂)
--     negate (f₁ ∨ f₂) = (¬ f₁) ∧ (¬ f₂)
--     negate (f₁ ➔ f₂) = f₁ ∧ (¬ f₂)
--     negate (⟨ x ⟩ f) = [ x ] (¬ f)
--     negate ([ x ] f) = ⟨ x ⟩ (¬ f)
-- x ⊢ (f₁ ∧ f₂) = x ⊢ f₁ × x ⊢ f₂
-- x ⊢ (f₁ ∨ f₂) = x ⊢ f₁ ⊎ x ⊢ f₂
-- x ⊢ (f₁ ➔ f₂) = x ⊢ f₁ → x ⊢ f₂
-- Pure _ ⊢ (⟨ _ ⟩ _) = ⊥
-- Step c₁ x ⊢ (⟨ c₂ ⟩ f) with c₁ ≟ c₂
-- ... | true = ∃[ r ] x r ⊢ f
-- ... | false = ⊥
-- Pure _ ⊢ ([ _ ] _) = ⊤
-- Step c₁ x ⊢ ([ c₂ ] f) with c₁ ≟ c₂
-- ... | true = ∀ r → x r ⊢ f
-- ... | false = ⊤

-- ATTEMPT 2: Manually remove the negation (good, but convoluted)
-- _⊢_ : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → Formula e → Set
-- _ ⊢ true = ⊤
-- _ ⊢ false = ⊥
-- x ⊢ (¬ f) = negate+⊢ x f
--   where
--     negate+⊢ : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → Formula e → Set
--     negate+⊢ _ true = ⊥
--     negate+⊢ _ false = ⊤
--     negate+⊢ x (¬ f) = x ⊢ f
--     negate+⊢ x (f₁ ∧ f₂) = x ⊢ (¬ f₁) ⊎ x ⊢ (¬ f₂)
--     negate+⊢ x (f₁ ∨ f₂) = x ⊢ (¬ f₁) × x ⊢ (¬ f₂)
--     negate+⊢ x (f₁ ➔ f₂) = x ⊢ f₁ × x ⊢ (¬ f₂)
--     negate+⊢ (Pure _) (⟨ _ ⟩ _) = ⊤
--     negate+⊢ (Step c₁ x) (⟨ c₂ ⟩ f) with c₁ ≟ c₂
--     ... | true = ∀ r → x r ⊢ (¬ f)
--     ... | false = ⊤
--     negate+⊢ (Pure _) ([ _ ] _) = ⊥
--     negate+⊢ (Step c₁ x) ([ c₂ ] f) with c₁ ≟ c₂
--     ... | true = ∃[ r ] x r ⊢ (¬ f)
--     ... | false = ⊥
-- x ⊢ (f₁ ∧ f₂) = x ⊢ f₁ × x ⊢ f₂
-- x ⊢ (f₁ ∨ f₂) = x ⊢ f₁ ⊎ x ⊢ f₂
-- x ⊢ (f₁ ➔ f₂) = x ⊢ f₁ → x ⊢ f₂
-- Pure _ ⊢ (⟨ _ ⟩ _) = ⊥
-- Step c₁ x ⊢ (⟨ c₂ ⟩ f) with c₁ ≟ c₂
-- ... | true = ∃[ r ] x r ⊢ f
-- ... | false = ⊥
-- Pure _ ⊢ ([ _ ] _) = ⊤
-- Step c₁ x ⊢ ([ c₂ ] f) with c₁ ≟ c₂
-- ... | true = ∀ r → x r ⊢ f
-- ... | false = ⊤

-- ATTEMPT 3: Use a helper type Formula' which doesn't have negation (good, but requires an extra type)
-- data Formula' (e : Effect) : Set where
--   true' false' : Formula' e
--   _∧'_ _∨'_ _➔'_ : Formula' e → Formula' e → Formula' e
--   ⟨_⟩'_ [_]'_ : (Effect.C e) → Formula' e → Formula' e

-- formula' : {e : Effect} → Formula e → Formula' e
-- formula' true = true'
-- formula' false = false'
-- formula' (¬ f) = negate f
--   where
--     negate : {e : Effect} → Formula e → Formula' e
--     negate true = false'
--     negate false = true'
--     negate (¬ f) = formula' f
--     negate (f₁ ∧ f₂) = formula' (¬ f₁) ∨' formula' (¬ f₂)
--     negate (f₁ ∨ f₂) = formula' (¬ f₁) ∧' formula' (¬ f₂)
--     negate (f₁ ➔ f₂) = formula' f₁ ∧' formula' (¬ f₂)
--     negate (⟨ x ⟩ f) = [ x ]' formula' (¬ f)
--     negate ([ x ] f) = ⟨ x ⟩' formula' (¬ f)
-- formula' (f₁ ∧ f₂) = formula' f₁ ∧' formula' f₂
-- formula' (f₁ ∨ f₂) = formula' f₁ ∨' formula' f₂
-- formula' (f₁ ➔ f₂) = formula' f₁ ➔' formula' f₂
-- formula' (⟨ x ⟩ f) = ⟨ x ⟩' formula' f
-- formula' ([ x ] f) = [ x ]' formula' f

-- _⊢_ : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → Formula e → Set
-- x ⊢ f = x ⊢' formula' f
--   where
--     _⊢'_ : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → Formula' e → Set
--     _ ⊢' true' = ⊤
--     _ ⊢' false' = ⊥
--     x ⊢' (f₁ ∧' f₂) = x ⊢' f₁ × x ⊢' f₂
--     x ⊢' (f₁ ∨' f₂) = x ⊢' f₁ ⊎ x ⊢' f₂
--     x ⊢' (f₁ ➔' f₂) = x ⊢' f₁ → x ⊢' f₂
--     Pure _ ⊢' (⟨ _ ⟩' _) = ⊥
--     Step c₁ x ⊢' (⟨ c₂ ⟩' f) with c₁ ≟ c₂
--     ... | true = ∃[ r ] x r ⊢' f
--     ... | false = ⊥
--     Pure _ ⊢' ([ _ ]' _) = ⊤
--     Step c₁ x ⊢' ([ c₂ ]' f) with c₁ ≟ c₂
--     ... | true = ∀ r → x r ⊢' f
--     ... | false = ⊤

-- ATTEMPT 4: Define a custom well-founded _<_ relation for the Formula type
operations : {e : Effect} → (Formula e) → ℕ
operations true = 0
operations false = 0
operations (¬ f) = 1 + operations f
operations (f₁ ∧ f₂) = 1 + operations f₁ + operations f₂
operations (f₁ ∨ f₂) = 1 + operations f₁ + operations f₂
operations (f₁ ➔ f₂) = 1 + operations f₁ + operations f₂
operations (⟨ _ ⟩ f) = 1 + operations f
operations ([ _ ] f) = 1 + operations f

_<_ : {e : Effect} → Rel (Formula e) 0ℓ
f₁ < f₂ = (operations f₁) <′ (operations f₂)

<-wf : {e : Effect} → WF.WellFounded (_<_ {e})
<-wf f = acc<′⇒acc< f (<′-wellFounded (operations f))
  where
    acc<′⇒acc< : {e : Effect} → (f : Formula e) → Acc _<′_ (operations f) → Acc _<_ f
    acc<′⇒acc< f₁ (acc h) = acc λ f₂ hlt → acc<′⇒acc< f₂ (h (operations f₂) hlt)

_⊢_ : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → Formula e → Set
x ⊢ f = helper x f (<-wf f)
  where
    negate : {e : Effect} → Formula e → Formula e
    negate true = false
    negate false = true
    negate (¬ f) = f
    negate (f₁ ∧ f₂) = negate f₁ ∨ negate f₂
    negate (f₁ ∨ f₂) = negate f₁ ∧ negate f₂
    negate (f₁ ➔ f₂) = f₁ ∧ negate f₂
    negate (⟨ x ⟩ f) = [ x ] negate f
    negate ([ x ] f) = ⟨ x ⟩ negate f

    [m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ : ∀ {m m′ n n′} → m ≤′ m′ → n ≤′ n′ → m + n ≤′ m′ + n′
    [m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ {zero} ≤′-refl hn = hn
    [m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ {suc m} ≤′-refl hn = s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ ≤′-refl hn)
    [m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ (≤′-step hm) hn = ≤′-step ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ hm hn)

    negate≤ : {e : Effect} → ∀ (f : Formula e) → operations (negate f) ≤′ operations f
    negate≤ true = ≤′-refl
    negate≤ false = ≤′-refl
    negate≤ (¬ f) = ≤′-step ≤′-refl
    negate≤ (f₁ ∧ f₂) = s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ (negate≤ f₁) (negate≤ f₂))
    negate≤ (f₁ ∨ f₂) = s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ (negate≤ f₁) (negate≤ f₂))
    negate≤ (f₁ ➔ f₂) = s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ ≤′-refl (negate≤ f₂))
    negate≤ (⟨ _ ⟩ f) = s≤′s (negate≤ f)
    negate≤ ([ _ ] f) = s≤′s (negate≤ f)

    negate<¬ : {e : Effect} → ∀ (f : Formula e) → (negate f) < (¬ f)
    negate<¬ true = ≤′-refl
    negate<¬ false = ≤′-refl
    negate<¬ (¬ f) = ≤′-step ≤′-refl
    negate<¬ (f₁ ∧ f₂) = s≤′s (s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ (negate≤ f₁) (negate≤ f₂)))
    negate<¬ (f₁ ∨ f₂) = s≤′s (s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ (negate≤ f₁) (negate≤ f₂)))
    negate<¬ (f₁ ➔ f₂) = s≤′s (s≤′s ([m≤′m′∧n≤′n′]⇒m+n≤′m′+n′ ≤′-refl (negate≤ f₂)))
    negate<¬ (⟨ x ⟩ f) = s≤′s (s≤′s (negate≤ f))
    negate<¬ ([ x ] f) = s≤′s (s≤′s (negate≤ f))

    m≤′n⇒m<′1+n : ∀ {m n} → m ≤′ n → m <′ suc n
    m≤′n⇒m<′1+n ≤′-refl = ≤′-refl
    m≤′n⇒m<′1+n (≤′-step h) = ≤′-step (s≤′s h)

    helper : {e : Effect} ⦃ _ : Decide e ⦄ → {a : Set} → Free e a → (f : Formula e) → Acc _<_ f → Set
    helper _ true _ = ⊤
    helper _ false _ = ⊥
    helper x (¬ f) (acc h) = helper x (negate f) (h (negate f) (negate<¬ f))
    helper x (f₁ ∧ f₂) (acc h) = helper x f₁ (h f₁ (m≤′n⇒m<′1+n (m≤′m+n (operations f₁) (operations f₂)))) × helper x f₂ (h f₂ (m≤′n⇒m<′1+n (n≤′m+n (operations f₁) (operations f₂))))
    helper x (f₁ ∨ f₂) (acc h) = helper x f₁ (h f₁ (m≤′n⇒m<′1+n (m≤′m+n (operations f₁) (operations f₂)))) ⊎ helper x f₂ (h f₂ (m≤′n⇒m<′1+n (n≤′m+n (operations f₁) (operations f₂))))
    helper x (f₁ ➔ f₂) (acc h) = helper x f₁ (h f₁ (m≤′n⇒m<′1+n (m≤′m+n (operations f₁) (operations f₂)))) → helper x f₂ (h f₂ (m≤′n⇒m<′1+n (n≤′m+n (operations f₁) (operations f₂))))
    helper (Pure _) (⟨ _ ⟩ _) _ = ⊥
    helper (Step c₁ x) (⟨ c₂ ⟩ f) _ with c₁ ≟ c₂
    ... | true = ∃[ r ] x r ⊢ f
    ... | false = ⊥
    helper (Pure _) ([ _ ] _) _ = ⊤
    helper (Step c₁ x) ([ c₂ ] f) _ with c₁ ≟ c₂
    ... | true = ∀ r → x r ⊢ f
    ... | false = ⊤
