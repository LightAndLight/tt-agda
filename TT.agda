module TT where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Maybe using (Maybe; just; map)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)

mutual
  data tt⇒ : ℕ → Set where
    var : ∀{n} → Fin n → tt⇒ n
    app : ∀{n} → tt⇒ n → tt⇐ n → tt⇒ n
    ann : ∀{n} → tt⇐ n → tt⇐ n → tt⇒ n

  data tt⇐ : ℕ → Set where
    lam : ∀{n} → tt⇐ (suc n) → tt⇐ n
    pi : ∀{n} → tt⇐ n → tt⇐ (suc n) → tt⇐ n
    type : ∀{n} → tt⇐ n
    embed : ∀{n} → tt⇒ n → tt⇐ n

mutual
  rename⇒ : ∀{n m} → (Fin n → Fin m) → tt⇒ n → tt⇒ m
  rename⇒ f (var x) = var (f x)
  rename⇒ f (ann t t₁) = ann (rename⇐ f t) (rename⇐ f t₁)
  rename⇒ f (app t t₁) = app (rename⇒ f t) (rename⇐ f t₁)

  rename⇐ : ∀{n m} → (Fin n → Fin m) → tt⇐ n → tt⇐ m
  rename⇐ f (lam t) = lam (rename⇐ (λ { zero → zero; (suc n) → suc (f n) }) t)
  rename⇐ f (pi t t₁) = pi (rename⇐ f t) (rename⇐ (λ { zero → zero; (suc n) → suc (f n) }) t₁)
  rename⇐ _ type = type
  rename⇐ f (embed a) = embed (rename⇒ f a)

mutual
  subst⇒ : ∀{n m} → (Fin n → tt⇒ m) → tt⇒ n → tt⇒ m
  subst⇒ f (var x) = f x
  subst⇒ f (ann t t₁) = ann (subst⇐ f t) (subst⇐ f t₁)
  subst⇒ f (app t t₁) = app (subst⇒ f t) (subst⇐ f t₁)

  subst⇐ : ∀{n m} → (Fin n → tt⇒ m) → tt⇐ n → tt⇐ m
  subst⇐ f (lam t) = lam (subst⇐ ( λ { zero → var zero; (suc n) → rename⇒ suc (f n) }) t)
  subst⇐ _ type = type
  subst⇐ f (pi t t₁) = pi (subst⇐ f t) ((subst⇐ ( λ { zero → var zero; (suc n) → rename⇒ suc (f n) }) t₁))
  subst⇐ f (embed a) = embed (subst⇒ f a)

_[_]⇒ : ∀{n} → tt⇒ (suc n) → tt⇒ n → tt⇒ n
a [ b ]⇒ = subst⇒ (λ { zero → b; (suc n) → var n }) a

_[_]⇐ : ∀{n} → tt⇐ (suc n) → tt⇒ n → tt⇐ n
a [ b ]⇐ = subst⇐ (λ { zero → b; (suc n) → var n }) a

infixl 30 _[_]⇒
infixl 30 _[_]⇐

mutual
  data value⇒ : ∀{n} → tt⇒ n → Set where
    value-var : ∀{n ix} → value⇒ {n} (var ix)
    value-ann : ∀{n} {x T : tt⇐ n} → value⇐ x → value⇐ T → value⇒ (ann x T)

  data value⇐ : ∀{n} → tt⇐ n → Set where
    value-lam : ∀{n e} → value⇐ {n} (lam e)
    value-pi : ∀{n S T} → value⇐ S → value⇐ {n} (pi S T)
    value-type : ∀{n} → value⇐ {n} type
    value-embed : ∀{n x} → value⇒ {n} x → value⇐ (embed x)

mutual
  data _↓-infer_ : ∀{n} → tt⇒ n → tt⇒ n → Set where
    step-app1 : ∀{n} {f f' : tt⇒ n} {x} → f ↓-infer f' → app f x ↓-infer app f' x
    step-app2 : ∀{n} {f : tt⇒ n} {x x'} → value⇒ f → x ↓-check x' → app f x ↓-infer app f x'
    step-beta :
      ∀{n} {e : tt⇐ (suc n)} {x S T} →
      value⇒ (ann (lam e) (pi S T)) →
      value⇐ x →
      app (ann (lam e) (pi S T)) x ↓-infer ann (e [ ann x S ]⇐) (T [ ann x S ]⇐)
    step-ann1 : ∀{n} {x T T' : tt⇐ n} → T ↓-check T' → ann x T ↓-infer ann x T'
    step-ann2 : ∀{n} {x x' T : tt⇐ n} → value⇐ T → x ↓-check x' → ann x T ↓-infer ann x' T

  data _↓-check_ : ∀{n} → tt⇐ n → tt⇐ n → Set where
    step-pi : ∀{n} {S S' : tt⇐ n} {T} → S ↓-check S' → pi S T ↓-check pi S' T
    step-embed : ∀{n} {x x' : tt⇒ n} → x ↓-infer x' → embed x ↓-check embed x'

mutual
  value-done-infer : ∀{n x x'} → value⇒ {n} x → x ↓-infer x' → ⊥
  value-done-infer value-var ()
  value-done-infer (value-ann _ v-T) (step-ann1 T-T') = value-done-check v-T T-T'
  value-done-infer (value-ann v-x _) (step-ann2 _ x-x') = value-done-check v-x x-x'

  value-done-check : ∀{n x x'} → value⇐ {n} x → x ↓-check x' → ⊥
  value-done-check value-lam ()
  value-done-check (value-pi v-x) (step-pi x-x') = value-done-check v-x x-x'
  value-done-check value-type ()
  value-done-check (value-embed v-x) (step-embed x-x') = value-done-infer v-x x-x'

data _↝-infer_ : ∀{n} → tt⇒ n → tt⇒ n → Set where
  eval-refl-infer : ∀{n} {a : tt⇒ n} → a ↝-infer a
  eval-trans-infer : ∀{n} {a a' a'' : tt⇒ n} → (a ↓-infer a') → (a' ↝-infer a'') → a ↝-infer a''

data _↝-check_ : ∀{n} → tt⇐ n → tt⇐ n → Set where
  eval-refl-check : ∀{n} {a : tt⇐ n} → a ↝-check a
  eval-trans-check : ∀{n} {a a' a'' : tt⇐ n} → (a ↓-check a') → (a' ↝-check a'') → a ↝-check a''

data ctx : ℕ → Set where
  ◆ : ctx 0
  _∷_ : ∀{n} → ctx n → (t : tt⇐ n) → ctx (suc n)

infixl 30 _∷_

data index : ∀{n} → Fin n → ctx n → tt⇐ n → Set where
  here : ∀{n rest t} → index {suc n} zero (rest ∷ t) (rename⇐ suc t)
  there :
    ∀{n ix rest t t'} →
    index {n} ix rest t →
    index (suc ix) (rest ∷ t') (rename⇐ suc t)

mutual
  data _⊢_⇐_ : ∀{n} → ctx n → tt⇐ n → tt⇐ n → Set where
    t-type : ∀{n} {Γ : ctx n} → Γ ⊢ type ⇐ type
    t-lam :
      ∀{n} {Γ : ctx n} {S S' T e} →
      (Γ ∷ S' ⊢ e ⇐ T) →
      Γ ⊢ lam e ⇐ pi S T
    t-pi :
      ∀{n} {Γ : ctx n} {S S' T} →
      (Γ ⊢ S ⇐ type) →
      (Γ ∷ S' ⊢ T ⇐ type) →
      Γ ⊢ pi S T ⇐ type
    t-embed : ∀{n} {Γ : ctx n} {x T} → (Γ ⊢ x ⇒ T) → Γ ⊢ embed x ⇐ T

  data _⊢_⇒_ : ∀{n} → ctx n → tt⇒ n → tt⇐ n → Set where
    t-var : ∀{n ix Γ T} → index {n} ix Γ T → Γ ⊢ var ix ⇒ T
    t-app :
      ∀{n} {Γ : ctx n} {S T f x} →
      (Γ ⊢ f ⇒ pi S T) →
      (Γ ⊢ x ⇐ S) →
      Γ ⊢ app f x ⇒ T [ ann x S ]⇐
    t-ann :
      ∀{n} {Γ : ctx n} {x T} →
      (Γ ⊢ T ⇐ type) →
      (Γ ⊢ x ⇐ T) →
      Γ ⊢ ann x T ⇒ T

mutual
  progress-⇐ :
    ∀{x T} →
    ◆ ⊢ x ⇐ T →
    (∃[ x' ] (x ↓-check x') ⊎ value⇐ x)
  progress-⇐ t-type = inr value-type
  progress-⇐ (t-lam t) = inr value-lam
  progress-⇐ (t-pi t t₁) with progress-⇐ t
  progress-⇐ (t-pi t t₁) | inl (S' , S-S') = inl (_ , step-pi S-S')
  progress-⇐ (t-pi t t₁) | inr v-S = inr (value-pi v-S)
  progress-⇐ (t-embed x) with progress-⇒ x
  progress-⇐ (t-embed x) | inl (x' , x-x') = inl (embed x' , step-embed x-x')
  progress-⇐ (t-embed x) | inr v-x = inr (value-embed v-x)

  progress-⇒ :
    ∀ {x T} →
    ◆ ⊢ x ⇒ T →
    (∃[ x' ] (x ↓-infer x') ⊎ value⇒ x)
  progress-⇒ (t-var x) = inr value-var
  progress-⇒ (t-app f x) with progress-⇒ f
  progress-⇒ (t-app f x) | inl (f' , f-f') = inl (_ , step-app1 f-f')
  progress-⇒ (t-app f x) | inr v-f with progress-⇐ x
  progress-⇒ (t-app f x) | inr v-f | inl (x' , x-x') = inl (_ , step-app2 v-f x-x')
  progress-⇒ (t-app (t-var ()) x) | inr value-var | inr v-x
  progress-⇒ (t-app (t-ann pi-type ()) x) | inr (value-ann (value-pi a) T) | inr v-x
  progress-⇒ (t-app (t-ann pi-type ()) x) | inr (value-ann value-type T) | inr v-x
  progress-⇒ (t-app (t-ann pi-type x-pi) x) | inr (value-ann (value-embed e) T) | inr v-x = {!!}
  progress-⇒ (t-app (t-ann pi-type (t-lam e-T)) x) | inr (value-ann value-lam T) | inr v-x =
    inl (_ , step-beta (value-ann value-lam T) v-x)
  progress-⇒ (t-ann x₁ x₂) = {!!}

strong-normalisation-infer :
  ∀{n} {Γ : ctx n} {x T} →
  Γ ⊢ x ⇒ T →
  ∃[ x' ] (x ↝-infer x' × value⇒ x')
strong-normalisation-infer = {!!}

strong-normalisation-check :
  ∀{n} {Γ : ctx n} {x T} →
  Γ ⊢ x ⇐ T →
  ∃[ x' ] (x ↝-check x' × value⇐ x')
strong-normalisation-check = {!!}

preservation-⇐ :
  ∀{n} {Γ : ctx n} {x x' T} →
  Γ ⊢ x ⇐ T →
  x ↓-check x' →
  Γ ⊢ x' ⇐ T
preservation-⇐ t x-x' = {!!}
