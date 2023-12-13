module ModalLogics.HennessyMilnerLogic.Properties where

open import Common.Effect
open import Common.Free
open import Common.Utils
open import Data.Empty using () renaming (⊥-elim to ⊥-elim₀)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_∘_; const; case_of_)
open import Level using (lift)
open import ModalLogics.HennessyMilnerLogic.Base
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open Effect
open _⇔_
open Eq ⦃...⦄

private variable
  ε : Effect
  α : Set

-- Proposition Logic

-- Theorems for ~_

~true⇔false : ⦃ _ : Eq (C ε) ⦄ → (x : Free ε α) → ~ true ⊢ x ⇔ false ⊢ x
to (~true⇔false _) h = ⊥-elim₀ (h tt)
from (~true⇔false _) h = ⊥-elim h

~false⇔true : ⦃ _ : Eq (C ε) ⦄ → (x : Free ε α) → ~ false ⊢ x ⇔ true ⊢ x
to (~false⇔true _) _ = tt
from (~false⇔true _) _ h = ⊥-elim h

~~f⇔f : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → ~ ~ f ⊢ x ⇔ f ⊢ x
to (~~f⇔f f x) ¬¬h with ⊢-dec f x
... | no ¬h = ⊥-elim₀ (¬¬h ¬h)
... | yes h = h
from (~~f⇔f _ _) h ¬h = ¬h h

~|f₁∧f₂|⇔~f₁∨~f₂ : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → ~ (f₁ ∧ f₂) ⊢ x ⇔ ~ f₁ ∨ ~ f₂ ⊢ x
to (~|f₁∧f₂|⇔~f₁∨~f₂ f₁ f₂ x) h with ⊢-dec f₁ x
... | no ¬h₁ = inj₁ ¬h₁
... | yes h₁ with ⊢-dec f₂ x
...   | no ¬h₂ = inj₂ ¬h₂
...   | yes h₂ = ⊥-elim₀ (h (h₁ , h₂))
from (~|f₁∧f₂|⇔~f₁∨~f₂ _ _ _) (inj₁ ¬h₁) (h₁ , _) = ⊥-elim₀ (¬h₁ h₁)
from (~|f₁∧f₂|⇔~f₁∨~f₂ _ _ _) (inj₂ ¬h₂) (_ , h₂) = ⊥-elim₀ (¬h₂ h₂)

~|f₁∨f₂|⇔~f₁∧~f₂ : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → ~ (f₁ ∨ f₂) ⊢ x ⇔ ~ f₁ ∧ ~ f₂ ⊢ x
to (~|f₁∨f₂|⇔~f₁∧~f₂ _ _ _) h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)
from (~|f₁∨f₂|⇔~f₁∧~f₂ _ _ _) (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
from (~|f₁∨f₂|⇔~f₁∧~f₂ _ _ _) (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for _∧_

f∧f⇔f : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∧ f ⊢ x ⇔ f ⊢ x
to (f∧f⇔f _ _) (h , _) = h
from (f∧f⇔f _ _) h = h , h

f₁∧f₂⇔f₂∧f₁ : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → f₁ ∧ f₂ ⊢ x ⇔ f₂ ∧ f₁ ⊢ x
to (f₁∧f₂⇔f₂∧f₁ _ _ _) (h₁ , h₂) = h₂ , h₁
from (f₁∧f₂⇔f₂∧f₁ _ _ _) (h₂ , h₁) = h₁ , h₂

|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → (f₁ ∧ f₂) ∧ f₃ ⊢ x ⇔ f₁ ∧ (f₂ ∧ f₃) ⊢ x
to (|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| _ _ _ _) ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃
from (|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| _ _ _ _) (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → f₁ ∧ (f₂ ∨ f₃) ⊢ x ⇔ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) ⊢ x
to (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
to (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)
from (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
from (f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| _ _ _ _) (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

f∧true⇔f : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∧ true ⊢ x ⇔ f ⊢ x
to (f∧true⇔f _ _) (h , _) = h
from (f∧true⇔f _ _) h = h , tt

f∧false⇔false : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∧ false ⊢ x ⇔ false ⊢ x
to (f∧false⇔false _ _) ()
from (f∧false⇔false _ _) ()

-- Theorems for _∨_

f∨f⇔f : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∨ f ⊢ x ⇔ f ⊢ x
to (f∨f⇔f _ _) (inj₁ h) = h
to (f∨f⇔f _ _) (inj₂ h) = h
from (f∨f⇔f _ _) h = inj₁ h

f₁∨f₂⇔f₂∨f₁ : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → f₁ ∨ f₂ ⊢ x ⇔ f₂ ∨ f₁ ⊢ x
to (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₁ h₁) = inj₂ h₁
to (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₂ h₂) = inj₁ h₂
from (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₁ h₂) = inj₂ h₂
from (f₁∨f₂⇔f₂∨f₁ _ _ _) (inj₂ h₁) = inj₁ h₁

|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → (f₁ ∨ f₂) ∨ f₃ ⊢ x ⇔ f₁ ∨ (f₂ ∨ f₃) ⊢ x
to (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₁ (inj₁ h₁)) = inj₁ h₁
to (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
to (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₂ h₃) = inj₂ (inj₂ h₃)
from (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₁ h₁) = inj₁ (inj₁ h₁)
from (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
from (|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| _ _ _ _) (inj₂ (inj₂ h₃)) = inj₂ h₃

f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ f₃ : Formula ε) → (x : Free ε α) → f₁ ∨ (f₂ ∧ f₃) ⊢ x ⇔ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) ⊢ x
to (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
to (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃
from (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₁ h₁ , _) = inj₁ h₁
from (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (_ , inj₁ h₁) = inj₁ h₁
from (f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| _ _ _ _) (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

f∨true⇔true : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∨ true ⊢ x ⇔ true ⊢ x
to (f∨true⇔true _ _) _ = tt
from (f∨true⇔true _ _) _ = inj₂ tt

f∨false⇔f : ⦃ _ : Eq (C ε) ⦄ → (f : Formula ε) → (x : Free ε α) → f ∨ false ⊢ x ⇔ f ⊢ x
to (f∨false⇔f _ _) (inj₁ h) = h
from (f∨false⇔f _ _) h = inj₁ h

-- Theorems for _⇒_

f₁⇒f₂⇔~f₁∨f₂ : ⦃ _ : Eq (C ε) ⦄ → (f₁ f₂ : Formula ε) → (x : Free ε α) → f₁ ⇒ f₂ ⊢ x ⇔ ~ f₁ ∨ f₂ ⊢ x
to (f₁⇒f₂⇔~f₁∨f₂ f₁ _ x) h with ⊢-dec f₁ x
... | no ¬h₁ = inj₁ ¬h₁
... | yes h₁ = inj₂ (h h₁)
from (f₁⇒f₂⇔~f₁∨f₂ _ _ _) (inj₁ ¬h₁) h₁ = ⊥-elim₀ (¬h₁ h₁)
from (f₁⇒f₂⇔~f₁∨f₂ _ _ _) (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

~|⟨c⟩f|⇔[c]~f : ⦃ eq : Eq (C ε) ⦄ → (c : C ε) → (f : Formula ε) → (x : Free ε α) → ~ (⟨ c ⟩ f) ⊢ x ⇔ [ c ] ~ f ⊢ x
to (~|⟨c⟩f|⇔[c]~f _ _ (pure _)) _ = tt
to (~|⟨c⟩f|⇔[c]~f c₁ _ (step c₂ _)) h¬∃ with c₁ == c₂
... | no _ = tt
... | yes refl = λ r h → h¬∃ (r , h)
from (~|⟨c⟩f|⇔[c]~f c₁ _ (step c₂ _)) _ h∃ with c₁ == c₂
... | no _ = ⊥-elim h∃
from (~|⟨c⟩f|⇔[c]~f c₁ _ (step .c₁ _)) h¬∀ (r , h) | yes refl = (h¬∀ r) h

⟨c⟩false⇔false : ⦃ eq : Eq (C ε) ⦄ → (c : C ε) → (x : Free ε α) → ⟨ c ⟩ false ⊢ x ⇔ false ⊢ x
to (⟨c⟩false⇔false c₁ (step c₂ _)) h∃ with c₁ == c₂
... | no _ = ⊥-elim h∃
to (⟨c⟩false⇔false c₁ (step .c₁ _)) () | yes refl
from (⟨c⟩false⇔false _ _) ()

⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| : ⦃ _ : Eq (C ε) ⦄ → (c : C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → ⟨ c ⟩ f₁ ∨ f₂ ⊢ x ⇔ (⟨ c ⟩ f₁) ∨ (⟨ c ⟩ f₂) ⊢ x
to (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step c₂ _)) h∃ with c₁ == c₂
... | no _ = ⊥-elim h∃
to (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step c₁ _)) (r , inj₁ h₁) | yes refl = inj₁ (r , h₁)
to (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step c₁ _)) (r , inj₂ h₂) | yes refl = inj₂ (r , h₂)
from (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step c₂ _)) (inj₁ h∃₁) with c₁ == c₂
... | no _ = ⊥-elim h∃₁
from (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step .c₁ _)) (inj₁ (r , h₁)) | yes refl = (r , inj₁ h₁)
from (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step c₂ _)) (inj₂ h∃₂) with c₁ == c₂
... | no _ = ⊥-elim h∃₂
from (⟨c⟩f₁∨f₂⇔|⟨c⟩f₁|∨|⟨c⟩f₂| c₁ _ _ (step .c₁ _)) (inj₂ (r , h₂)) | yes refl = (r , inj₂ h₂)

|⟨c⟩f₁|∧|[c]f₂|→⟨c⟩f₁∧f₂ : ⦃ _ : Eq (C ε) ⦄ → (c : C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → (⟨ c ⟩ f₁) ∧ ([ c ] f₂) ⊢ x → ⟨ c ⟩ f₁ ∧ f₂ ⊢ x
|⟨c⟩f₁|∧|[c]f₂|→⟨c⟩f₁∧f₂ c₁ _ _ (step c₂ _) _ with c₁ == c₂
|⟨c⟩f₁|∧|[c]f₂|→⟨c⟩f₁∧f₂ c₁ _ _ (step c₂ _) () | no _
|⟨c⟩f₁|∧|[c]f₂|→⟨c⟩f₁∧f₂ c₁ _ _ (step c₁ _) ((r , h₁) , h∀₂) | yes refl = r , h₁ , h∀₂ r

-- Theorems for [_]_

~|[c]f|⇔⟨c⟩~f : ⦃ _ : Eq (C ε) ⦄ → (c : C ε) → (f : Formula ε) → (x : Free ε α) → ~ ([ c ] f) ⊢ x ⇔ ⟨ c ⟩ ~ f ⊢ x
to (~|[c]f|⇔⟨c⟩~f c f (pure _)) h¬∀ = lift (h¬∀ tt)
to (~|[c]f|⇔⟨c⟩~f c₁ f (step c₂ k)) h¬∀ with ⊢-dec (⟨ c₁ ⟩ ~ f) (step c₂ k)
... | yes h∃ = h∃
... | no h¬∃ with c₁ == c₂
...   | no _ = lift (h¬∀ tt)
...   | yes refl = ⊥-elim₀ (h¬∀ λ r → case ⊢-dec f (k r) of λ { (yes h) → h ; (no ¬h) → ⊥-elim₀ (h¬∃ (r , ¬h)) })
from (~|[c]f|⇔⟨c⟩~f c₁ _ (step c₂ _)) h∃ _ with c₁ == c₂
... | no _ = ⊥-elim h∃
from (~|[c]f|⇔⟨c⟩~f c₁ _ (step .c₁ _)) (r , ¬h) h∀ | yes refl = ¬h (h∀ r)

[c]true⇔true : ⦃ _ : Eq (C ε) ⦄ → (c : C ε) → (x : Free ε α) → [ c ] true ⊢ x ⇔ true ⊢ x
to ([c]true⇔true _ _) _ = tt
from ([c]true⇔true _ (pure _)) _ = tt
from ([c]true⇔true c₁ (step c₂ _)) _ with c₁ == c₂
... | no _ = tt
... | yes refl = const tt

[c]f₁∧f₂⇔|[c]f₁|∧|[c]f₂| : ⦃ _ : Eq (C ε) ⦄ → (c : C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → [ c ] f₁ ∧ f₂ ⊢ x ⇔ ([ c ] f₁) ∧ ([ c ] f₂) ⊢ x
to ([c]f₁∧f₂⇔|[c]f₁|∧|[c]f₂| _ _ _ (pure _)) _ = tt , tt
to ([c]f₁∧f₂⇔|[c]f₁|∧|[c]f₂| c₁ _ _ (step c₂ _)) h∀ with c₁ == c₂
... | no _ = tt , tt
... | yes refl = (proj₁ ∘ h∀) , (proj₂ ∘ h∀)
from ([c]f₁∧f₂⇔|[c]f₁|∧|[c]f₂| _ _ _ (pure _)) _ = tt
from ([c]f₁∧f₂⇔|[c]f₁|∧|[c]f₂| c₁ _ _ (step c₂ _)) _ with c₁ == c₂
... | no _ = tt
from ([c]f₁∧f₂⇔|[c]f₁|∧|[c]f₂| c₁ _ _ (step .c₁ _)) (h∀₁ , h∀₂) | yes refl = λ r → h∀₁ r , h∀₂ r 

[c]f₁∨f₂→|⟨c⟩f₁|∨|[c]f₂| : ⦃ _ : Eq (C ε) ⦄ → (c : C ε) → (f₁ f₂ : Formula ε) → (x : Free ε α) → [ c ] f₁ ∨ f₂ ⊢ x → (⟨ c ⟩ f₁) ∨ ([ c ] f₂) ⊢ x
[c]f₁∨f₂→|⟨c⟩f₁|∨|[c]f₂| _ _ _ (pure _) _ = inj₂ tt
[c]f₁∨f₂→|⟨c⟩f₁|∨|[c]f₂| c₁ f₁ f₂ x@(step c₂ k) h with ⊢-dec (⟨ c₁ ⟩ f₁) x
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊢-dec ([ c₁ ] f₂) x
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with c₁ == c₂
...     | no _ = inj₂ tt
...     | yes _ = ⊥-elim₀ (h¬∀ λ r → case h r of λ { (inj₁ h₁) → ⊥-elim₀ (h¬∃ (r , h₁)) ; (inj₂ h₂) → h₂ })
