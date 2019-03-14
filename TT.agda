module TT where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Maybe using (Maybe; just; map)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)

-- This takes the load off. Thanks, Conor!
data sort : Set where
  check : sort
  infer : sort

data tt : sort → ℕ → Set where
  var : ∀{n} → Fin n → tt infer n
  app : ∀{n} → tt infer n → tt check n → tt infer n
  ann : ∀{n} → tt check n → tt check n → tt infer n

  lam : ∀{n} → tt check (suc n) → tt check n
  pi : ∀{n} → tt check n → tt check (suc n) → tt check n
  type : ∀{n} → tt check n
  embed : ∀{n} → tt infer n → tt check n

rename : ∀{s n m} → (Fin n → Fin m) → tt s n → tt s m
rename f (var x) = var (f x)
rename f (ann t t₁) = ann (rename f t) (rename f t₁)
rename f (app t t₁) = app (rename f t) (rename f t₁)
rename f (lam t) = lam (rename (λ { zero → zero; (suc n) → suc (f n) }) t)
rename f (pi t t₁) = pi (rename f t) (rename (λ { zero → zero; (suc n) → suc (f n) }) t₁)
rename _ type = type
rename f (embed a) = embed (rename f a)

subst : ∀{s n m} → (Fin n → tt infer m) → tt s n → tt s m
subst f (var x) = f x
subst f (ann t t₁) = ann (subst f t) (subst f t₁)
subst f (app t t₁) = app (subst f t) (subst f t₁)
subst f (lam t) = lam (subst ( λ { zero → var zero; (suc n) → rename suc (f n) }) t)
subst _ type = type
subst f (pi t t₁) = pi (subst f t) ((subst ( λ { zero → var zero; (suc n) → rename suc (f n) }) t₁))
subst f (embed a) = embed (subst f a)

_[_] : ∀{s n} → tt s (suc n) → tt infer n → tt s n
a [ b ] = subst (λ { zero → b; (suc n) → var n }) a

infixl 30 _[_]

data has-ann : Set where
  allow-ann : has-ann
  block-ann : has-ann

data value (n : ℕ) : has-ann → (s : sort) → tt s n → Set where
  value-var : ∀{a ix} → value n a infer (var ix)
  -- if we allow variables to be values, then
  -- applications must also be values
  value-app :
    ∀{a f x} →
    value n a infer f →
    value n a check x →
    value n a infer (app f x)
  value-ann :
    ∀{a x T} →
    value n block-ann infer x →
    value n a check T →
    value n allow-ann infer (ann (embed x) T)
  value-lam :
    ∀{a e} →
    value (suc n) a check e →
    value n a check (lam e)
  value-pi :
    ∀{a S T} →
    value n a check S →
    value (suc n) a check T →
    value n a check (pi S T)
  value-type : ∀{a} → value n a check type
  value-embed : ∀{a e} → value n block-ann infer e → value n a check (embed e)

data _↓_ {n : ℕ} : {s : sort} → tt s n → tt s n → Set where
  step-app1 :
    ∀{f f' : tt infer n} {x : tt check n} →
    f ↓ f' →
    app f x ↓ app f' x
  step-app2 :
    ∀{a} {f : tt infer n} {x x' : tt check n} →
    value n a infer f →
    x ↓ x' →
    app f x ↓ app f x'
  step-beta :
    ∀{a} {e : tt check (suc n)} {x S : tt check n} {T : tt check (suc n)} →
    value n allow-ann infer (ann (lam e) (pi S T)) →
    value n a check x →
    app (ann (lam e) (pi S T)) x ↓ ann (e [ ann x S ]) (T [ ann x S ])
  step-upsilon :
    ∀{a x T} →
    value n a check x →
    value n a check T →
    embed (ann x T) ↓ x
  step-ann1 : ∀{a} {x x' T : tt check n} → value n a check T → x ↓ x' → ann x T ↓ ann x' T
  step-ann2 : ∀{x T T' : tt check n} → T ↓ T' → ann x T ↓ ann x T'

  step-lam : ∀{e e' : tt check (suc n)} → e ↓ e' → lam e ↓ lam e'
  step-pi1 : ∀{S S' : tt check n} {T} → S ↓ S' → pi S T ↓ pi S' T
  step-pi2 : ∀{a} {S : tt check n} {T T'} → value n a check S → T ↓ T' → pi S T ↓ pi S T'
  step-embed : ∀{x x' : tt infer n} → x ↓ x' → embed x ↓ embed x'

value-done : ∀{a s n} {x x' : tt s n} → value n a s x → x ↓ x' → ⊥
value-done value-var ()
value-done (value-lam x-v) (step-lam x-x') = value-done x-v x-x'
value-done (value-pi v-S v-T) (step-pi1 S-S') = value-done v-S S-S'
value-done (value-pi v-S v-T) (step-pi2 _ T-T') = value-done v-T T-T'
value-done value-type ()
value-done (value-embed ()) (step-upsilon x x₁)
value-done {a} (value-embed value-var) (step-embed x-x') = value-done {a} value-var x-x'
value-done (value-embed (value-app v-f v-x)) (step-embed x-x') = value-done (value-app v-f v-x) x-x'
value-done (value-app v-f v-x) (step-app1 x-x') = value-done v-f x-x'
value-done (value-app v-f v-x) (step-app2 _ x-x') = value-done v-x x-x'
value-done (value-app () v-x) (step-beta l lm)
value-done {a} (value-ann v-x v-T) (step-ann1 _ x-x') = value-done {a} (value-embed v-x) x-x'
value-done (value-ann v-x v-T) (step-ann2 x-x') = value-done v-T x-x'

data _↝_ {n : ℕ} : ∀{s} → tt s n → tt s n → Set where
  eval-refl-infer : ∀{s} {a : tt s n} → a ↝ a
  eval-trans-infer : ∀{s} {a a' a'' : tt s n} → (a ↓ a') → (a' ↝ a'') → a ↝ a''

data ctx : ℕ → Set where
  ◆ : ctx 0
  _∷_ : ∀{n} → ctx n → (t : tt check n) → ctx (suc n)

infixl 30 _∷_

data index : ∀{n} → Fin n → ctx n → tt check n → Set where
  here : ∀{n rest t} → index {suc n} zero (rest ∷ t) (rename suc t)
  there :
    ∀{n ix rest t t'} →
    index {n} ix rest t →
    index (suc ix) (rest ∷ t') (rename suc t)

data _⊢_∶_ {n : ℕ} : ∀{s} → ctx n → tt s n → tt check n → Set where
  t-type : ∀{Γ : ctx n} → Γ ⊢ type ∶ type
  t-lam :
    ∀{Γ : ctx n} {S S' T e} →
    (Γ ∷ S' ⊢ e ∶ T) →
    Γ ⊢ lam e ∶ pi S T
  t-pi :
    ∀{Γ : ctx n} {S S' T} →
    (Γ ⊢ S ∶ type) →
    (Γ ∷ S' ⊢ T ∶ type) →
    Γ ⊢ pi S T ∶ type
  t-embed : ∀{Γ : ctx n} {x T} → (Γ ⊢ x ∶ T) → Γ ⊢ embed x ∶ T

  t-var : ∀{ix Γ T} → index {n} ix Γ T → Γ ⊢ var ix ∶ T
  t-app :
    ∀{Γ : ctx n} {S T f x} →
    (Γ ⊢ f ∶ pi S T) →
    (Γ ⊢ x ∶ S) →
    Γ ⊢ app f x ∶ T [ ann x S ]
  t-ann :
    ∀{Γ : ctx n} {x T} →
    (Γ ⊢ T ∶ type) →
    (Γ ⊢ x ∶ T) →
    Γ ⊢ ann x T ∶ T

progress :
  ∀{s n} {Γ : ctx n} {x : tt s n} {T : tt check n} →
  Γ ⊢ x ∶ T →
  (Σ[ x' ∈ tt s n ] (x ↓ x') ⊎ value n allow-ann s x)
progress t-type = inr value-type
progress (t-lam e) with progress e
progress (t-lam e) | inl (e' , e-e') = inl (lam e' , step-lam e-e')
progress (t-lam e) | inr v-e = inr (value-lam v-e)
progress (t-pi S T) with progress S
progress (t-pi S T) | inl (S' , S-S') = inl (_ , step-pi1 S-S')
progress (t-pi S T) | inr v-S with progress T
progress (t-pi S T) | inr v-S | inl (T' , T-T') = inl (_ , step-pi2 v-S T-T')
progress (t-pi S T) | inr v-S | inr v-T = inr (value-pi v-S v-T)
progress (t-var x) = inr value-var
progress (t-embed t) with progress t
progress (t-embed t) | inl (t' , t-t') = inl (embed t' , step-embed t-t')
progress (t-embed t) | inr v-t = {!!}
progress (t-app f a) with progress f
progress (t-app f a) | inl (f' , f-f') = inl (_ , step-app1 f-f')
progress (t-app f a) | inr v-f with progress a
progress (t-app f a) | inr v-f | inl (x' , x-x') = inl (_ , step-app2 v-f x-x')
progress (t-app f a) | inr v-f | inr v-a = {!!}
progress (t-ann x T) = {!!}

strong-normalisation :
  ∀{a s n} {Γ : ctx n} {x : tt s n} {T : tt check n} →
  Γ ⊢ x ∶ T →
  Σ[ x' ∈ tt s n ] (x ↝ x' × value n a s x')
strong-normalisation = {!!}

preservation-⇐ :
  ∀{s n} {Γ : ctx n} {x x' : tt s n} {T : tt check n} →
  Γ ⊢ x ∶ T →
  x ↓ x' →
  Γ ⊢ x' ∶ T
preservation-⇐ t x-x' = {!!}
