module ModalLogics.HennessyMilnerLogic.Properties where

open import Common.Effect
open import Common.Free
open import Common.Utils
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function.Base using (_∘_; const; case_of_)
open import ModalLogics.HennessyMilnerLogic.Base
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Nullary using (yes; no)

open Eq ⦃...⦄

variable
  ε : Effect
  α : Set

open _⇔_

-- Proposition Logic

-- Theorems for ~_

notTrueIffFalse : ⦃ _ : Eq (Effect.C ε) ⦄ → (x : Free ε α) → ~ true ⊢ x ⇔ false ⊢ x
to (notTrueIffFalse _) h = ⊥-elim (h tt)
from (notTrueIffFalse _) h = ⊥-elim h

notFalseIffTrue : ⦃ _ : Eq (Effect.C ε) ⦄ → (x : Free ε α) → ~ false ⊢ x ⇔ true ⊢ x
to (notFalseIffTrue _) _ = tt
from (notFalseIffTrue _) _ h = ⊥-elim h

notNotFIffF : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → ~ ~ f ⊢ x ⇔ f ⊢ x
to (notNotFIffF f x) ¬¬h with ⊢-dec f x
... | no ¬h = ⊥-elim (¬¬h ¬h)
... | yes h = h
from (notNotFIffF _ _) h ¬h = ¬h h

notAndIffNotOrNot : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → ~ f₁ ∧ f₂ ⊢ x ⇔ (~ f₁ ⊢ x ⊎ ~ f₂ ⊢ x)
to (notAndIffNotOrNot f₁ f₂ x) h with ⊢-dec f₁ x
... | no ¬h₁ = inj₁ ¬h₁
... | yes h₁ with ⊢-dec f₂ x
...   | no ¬h₂ = inj₂ ¬h₂
...   | yes h₂ = ⊥-elim (h (h₁ , h₂))
from (notAndIffNotOrNot _ _ _) (inj₁ ¬h₁) (h₁ , _) = ⊥-elim (¬h₁ h₁)
from (notAndIffNotOrNot _ _ _) (inj₂ ¬h₂) (_ , h₂) = ⊥-elim (¬h₂ h₂)

notOrIffNotAndNot : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → ~ f₁ ∨ f₂ ⊢ x ⇔ (~ f₁ ⊢ x × ~ f₂ ⊢ x)
to (notOrIffNotAndNot _ _ _) h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)
from (notOrIffNotAndNot _ _ _) (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
from (notOrIffNotAndNot _ _ _) (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for ∧

andRefl : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∧ f ⊢ x ⇔ f ⊢ x
to (andRefl _ _) (h , _) = h
from (andRefl _ _) h = h , h

andComm : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → f₁ ∧ f₂ ⊢ x ⇔ f₂ ∧ f₁ ⊢ x
to (andComm _ _ _) (h₁ , h₂) = h₂ , h₁
from (andComm _ _ _) (h₂ , h₁) = h₁ , h₂

andAssoc : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → (f₁ ∧ f₂) ∧ f₃ ⊢ x ⇔ f₁ ∧ (f₂ ∧ f₃) ⊢ x
to (andAssoc _ _ _ _) ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃
from (andAssoc _ _ _ _) (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

andDistrib : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → f₁ ∧ (f₂ ∨ f₃) ⊢ x ⇔ ((f₁ ∧ f₂) ⊢ x ⊎ (f₁ ∧ f₃) ⊢ x)
to (andDistrib _ _ _ _) (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
to (andDistrib _ _ _ _) (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)
from (andDistrib _ _ _ _) (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
from (andDistrib _ _ _ _) (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

andTrue : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∧ true ⊢ x ⇔ f ⊢ x
to (andTrue _ _) (h , _) = h
from (andTrue _ _) h = h , tt

andFalse : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∧ false ⊢ x ⇔ false ⊢ x
to (andFalse _ _) ()
from (andFalse _ _) ()

-- Theorems for ∨

orRefl : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∨ f ⊢ x ⇔ f ⊢ x
to (orRefl _ _) (inj₁ h) = h
to (orRefl _ _) (inj₂ h) = h
from (orRefl _ _) h = inj₁ h

orComm : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → f₁ ∨ f₂ ⊢ x ⇔ f₂ ∨ f₁ ⊢ x
to (orComm _ _ _) (inj₁ h₁) = inj₂ h₁
to (orComm _ _ _) (inj₂ h₂) = inj₁ h₂
from (orComm _ _ _) (inj₁ h₂) = inj₂ h₂
from (orComm _ _ _) (inj₂ h₁) = inj₁ h₁

orAssoc : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → (f₁ ∨ f₂) ∨ f₃ ⊢ x ⇔ f₁ ∨ (f₂ ∨ f₃) ⊢ x
to (orAssoc _ _ _ _) (inj₁ (inj₁ h₁)) = inj₁ h₁
to (orAssoc _ _ _ _) (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
to (orAssoc _ _ _ _) (inj₂ h₃) = inj₂ (inj₂ h₃)
from (orAssoc _ _ _ _) (inj₁ h₁) = inj₁ (inj₁ h₁)
from (orAssoc _ _ _ _) (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
from (orAssoc _ _ _ _) (inj₂ (inj₂ h₃)) = inj₂ h₃

orDistrib : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → f₁ ∨ (f₂ ∧ f₃) ⊢ x ⇔ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊢ x
to (orDistrib _ _ _ _) (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
to (orDistrib _ _ _ _) (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃
from (orDistrib _ _ _ _) (inj₁ h₁ , _) = inj₁ h₁
from (orDistrib _ _ _ _) (_ , inj₁ h₁) = inj₁ h₁
from (orDistrib _ _ _ _) (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

orTrue : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∨ true ⊢ x ⇔ true ⊢ x
to (orTrue _ _) _ = tt
from (orTrue _ _) _ = inj₂ tt

orFalse : ⦃ _ : Eq (Effect.C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∨ false ⊢ x ⇔ f ⊢ x
to (orFalse _ _) (inj₁ h) = h
from (orFalse _ _) h = inj₁ h

-- Other theorems

rwImplication : ⦃ _ : Eq (Effect.C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → (f₁ ⊢ x → f₂ ⊢ x) ⇔ (~ f₁) ∨ f₂ ⊢ x
to (rwImplication f₁ _ x) h with ⊢-dec f₁ x
... | no ¬h₁ = inj₁ ¬h₁
... | yes h₁ = inj₂ (h h₁)
from (rwImplication _ _ _) (inj₁ ¬h₁) h₁ = ⊥-elim (¬h₁ h₁)
from (rwImplication _ _ _) (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

notExistsIffForallNot : ⦃ eq : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (f : Formula ε) → (x : Free ε α) → ~ ⟨ c ⟩ f ⊢ x ⇔ [ c ] (~ f) ⊢ x
to (notExistsIffForallNot _ _ (pure _)) _ = tt
to (notExistsIffForallNot c₁ _ (step c₂ _)) h¬∃ with c₁ == c₂
... | no _ = tt
... | yes refl = λ r h → h¬∃ (r , h)
from (notExistsIffForallNot c₁ _ (step c₂ _)) _ h∃ with c₁ == c₂
... | no _ = ⊥-elim h∃
from (notExistsIffForallNot c₁ _ (step .c₁ _)) h¬∀ (r , h) | yes refl = (h¬∀ r) h

existsFalseIffFalse : ⦃ eq : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (x : Free ε α) → ⟨ c ⟩ false ⊢ x ⇔ false ⊢ x
to (existsFalseIffFalse c₁ (step c₂ _)) h∃ with c₁ == c₂
... | no _ = ⊥-elim h∃
to (existsFalseIffFalse c₁ (step .c₁ _)) () | yes refl
from (existsFalseIffFalse _ _) ()

existsOrIffExistsOrExists : ⦃ _ : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → ⟨ c ⟩ f₁ ∨ f₂ ⊢ x ⇔ (⟨ c ⟩ f₁ ⊢ x ⊎ ⟨ c ⟩ f₂ ⊢ x)
to (existsOrIffExistsOrExists c₁ _ _ (step c₂ _)) h∃ with c₁ == c₂
... | no _ = ⊥-elim h∃
to (existsOrIffExistsOrExists c₁ _ _ (step c₁ _)) (r , inj₁ h₁) | yes refl = inj₁ (r , h₁)
to (existsOrIffExistsOrExists c₁ _ _ (step c₁ _)) (r , inj₂ h₂) | yes refl = inj₂ (r , h₂)
from (existsOrIffExistsOrExists c₁ _ _ (step c₂ _)) (inj₁ h∃₁) with c₁ == c₂
... | no _ = ⊥-elim h∃₁
from (existsOrIffExistsOrExists c₁ _ _ (step .c₁ _)) (inj₁ (r , h₁)) | yes refl = (r , inj₁ h₁)
from (existsOrIffExistsOrExists c₁ _ _ (step c₂ _)) (inj₂ h∃₂) with c₁ == c₂
... | no _ = ⊥-elim h∃₂
from (existsOrIffExistsOrExists c₁ _ _ (step .c₁ _)) (inj₂ (r , h₂)) | yes refl = (r , inj₂ h₂)

existsAndofExistsAndForall : ⦃ _ : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → (⟨ c ⟩ f₁ ⊢ x × [ c ] f₂ ⊢ x) → ⟨ c ⟩ f₁ ∧ f₂ ⊢ x
existsAndofExistsAndForall c₁ _ _ (step c₂ _) _ with c₁ == c₂
existsAndofExistsAndForall c₁ _ _ (step c₂ _) () | no _
existsAndofExistsAndForall c₁ _ _ (step c₁ _) ((r , h₁) , h∀₂) | yes refl = r , h₁ , h∀₂ r

-- Theorems for [_]_

notForallIffExistsNot : ⦃ _ : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (f : Formula ε) → (x : Free ε α) → ~ [ c ] f ⊢ x ⇔ ⟨ c ⟩ (~ f) ⊢ x
to (notForallIffExistsNot c f (pure _)) h¬∀ = h¬∀ tt
to (notForallIffExistsNot c₁ f (step c₂ k)) h¬∀ with ⊢-dec (⟨ c₁ ⟩ (~ f)) (step c₂ k)
... | yes h∃ = h∃
... | no h¬∃ with c₁ == c₂
...   | no _ = h¬∀ tt
...   | yes refl = ⊥-elim (h¬∀ λ r → case ⊢-dec f (k r) of λ { (yes h) → h ; (no ¬h) → ⊥-elim (h¬∃ (r , ¬h)) })
from (notForallIffExistsNot c₁ _ (step c₂ _)) h∃ _ with c₁ == c₂
... | no _ = ⊥-elim h∃
from (notForallIffExistsNot c₁ _ (step .c₁ _)) (r , ¬h) h∀ | yes refl = ¬h (h∀ r)

forallTrueIffTrue : ⦃ _ : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (x : Free ε α) → [ c ] true ⊢ x ⇔ true ⊢ x
to (forallTrueIffTrue _ _) _ = tt
from (forallTrueIffTrue _ (pure _)) _ = tt
from (forallTrueIffTrue c₁ (step c₂ _)) _ with c₁ == c₂
... | no _ = tt
... | yes refl = const tt

forallAndIffForallAndForall : ⦃ _ : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → [ c ] f₁ ∧ f₂ ⊢ x ⇔ ([ c ] f₁ ⊢ x × [ c ] f₂ ⊢ x)
to (forallAndIffForallAndForall _ _ _ (pure _)) _ = tt , tt
to (forallAndIffForallAndForall c₁ _ _ (step c₂ _)) h∀ with c₁ == c₂
... | no _ = tt , tt
... | yes refl = (proj₁ ∘ h∀) , (proj₂ ∘ h∀)
from (forallAndIffForallAndForall _ _ _ (pure _)) _ = tt
from (forallAndIffForallAndForall c₁ _ _ (step c₂ _)) _ with c₁ == c₂
... | no _ = tt
from (forallAndIffForallAndForall c₁ _ _ (step .c₁ _)) (h∀₁ , h∀₂) | yes refl = λ r → h∀₁ r , h∀₂ r 

existsOrForallOfForallOr : ⦃ _ : Eq (Effect.C ε) ⦄ → (c : Effect.C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → [ c ] f₁ ∨ f₂ ⊢ x → (⟨ c ⟩ f₁ ⊢ x ⊎ [ c ] f₂ ⊢ x)
existsOrForallOfForallOr _ _ _ (pure _) _ = inj₂ tt
existsOrForallOfForallOr c₁ f₁ f₂ x@(step c₂ k) h with ⊢-dec (⟨ c₁ ⟩ f₁) x
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊢-dec ([ c₁ ] f₂) x
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with c₁ == c₂
...     | no _ = inj₂ tt
...     | yes _ = ⊥-elim (h¬∀ λ r → case h r of λ { (inj₁ h₁) → ⊥-elim (h¬∃ (r , h₁)) ; (inj₂ h₂) → h₂ })
