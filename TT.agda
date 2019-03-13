module TT where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; _∷_)
open import Data.Maybe using (Maybe; just; map)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)

data tt : ℕ → Set where
  var : ∀{n} → Fin n → tt n
  lam : ∀{n} → tt (suc n) → tt n
  app : ∀{n} → tt n → tt n → tt n
  pi : ∀{n} → tt n → tt (suc n) → tt n
  type : ∀{n} → tt n
  ann : ∀{n} → tt n → tt n → tt n

rename : ∀{n m} → (Fin n → Fin m) → tt n → tt m
rename f (var x) = var (f x)
rename f (lam t) = lam (rename (λ { zero → zero; (suc n) → suc (f n) }) t)
rename f (app t t₁) = app (rename f t) (rename f t₁)
rename f (ann t t₁) = ann (rename f t) (rename f t₁)
rename f (pi t t₁) = pi (rename f t) (rename (λ { zero → zero; (suc n) → suc (f n) }) t₁)
rename _ type = type

subst : ∀{n m} → (Fin n → tt m) → tt n → tt m
subst f (var x) = f x
subst f (lam t) = lam (subst ( λ { zero → var zero; (suc n) → rename suc (f n) }) t)
subst f (app t t₁) = app (subst f t) (subst f t₁)
subst f (ann t t₁) = ann (subst f t) (subst f t₁)
subst f (pi t t₁) = pi (subst f t) ((subst ( λ { zero → var zero; (suc n) → rename suc (f n) }) t₁))
subst _ type = type

_[_] : ∀{n} → tt (suc n) → tt n → tt n
a [ b ] = subst (λ { zero → b; (suc n) → var n }) a

infixl 30 _[_]

data value : ∀{n} → tt n → Set where
  value-lam : ∀{n e} → value {n} (lam e)
  value-pi : ∀{n S T} → value S → value {n} (pi S T)
  value-type : ∀{n} → value {n} type

data _↓_ : ∀{n} → tt n → tt n → Set where
  step-app1 : ∀{n} {f f' x : tt n} → f ↓ f' → app f x ↓ app f' x
  step-app2 : ∀{n} {f x x' : tt n} → value f → x ↓ x' → app f x ↓ app f x'
  step-beta : ∀{n} {e : tt (suc n)} {x} → value x → app (lam e) x ↓ e [ x ]
  step-pi : ∀{n} {S S' : tt n} {T} → S ↓ S' → pi S T ↓ pi S' T
  step-ann : ∀{n} {x : tt n} {T} → ann x T ↓ x

data _↝_ : ∀{n} → tt n → tt n → Set where
  eval-refl : ∀{n} {a : tt n} → a ↝ a
  eval-trans : ∀{n} {a a' a'' : tt n} → (a ↓ a') → (a' ↝ a'') → a ↝ a''

data ctx : ℕ → Set where
  ◆ : ctx 0
  _,_⟨_⟩ : ∀{n} → ctx n → (t : tt n) → value t → ctx (suc n)

infixl 30 _,_⟨_⟩

data index : ∀{n} → Fin n → ctx n → tt n → Set where
  here : ∀{n rest t v} → index {suc n} zero (rest , t ⟨ v ⟩) (rename suc t)
  there : ∀{n ix rest t t' v} → index {n} ix rest t → index (suc ix) (rest , t' ⟨ v ⟩) (rename suc t)

mutual
  data _⊢_⇐_ : ∀{n} → ctx n → tt n → tt n → Set where
    t-type : ∀{n} {Γ : ctx n} → Γ ⊢ type ⇐ type
    t-lam :
      ∀{n} {Γ : ctx n} {S S' T e} →
      (S ↝ S') →
      (v : value S') →
      (Γ , S' ⟨ v ⟩ ⊢ e ⇐ T) →
      Γ ⊢ lam e ⇐ pi S T
    t-pi :
      ∀{n} {Γ : ctx n} {S S' T} →
      (Γ ⊢ S ⇐ type) →
      (S ↝ S') →
      (v : value S') →
      (Γ , S' ⟨ v ⟩ ⊢ T ⇐ type) →
      Γ ⊢ pi S T ⇐ type
    t-embed : ∀{n} {Γ : ctx n} {x T T'} → (Γ ⊢ x ⇒ T) → (T ↝ T') → Γ ⊢ x ⇐ T'

  data _⊢_⇒_ : ∀{n} → ctx n → tt n → tt n → Set where
    t-var : ∀{n ix Γ T} → index {n} ix Γ T → Γ ⊢ var ix ⇒ T
    t-app :
      ∀{n} {Γ : ctx n} {S T f x} →
      (Γ ⊢ f ⇒ pi S T) →
      (Γ ⊢ x ⇐ S) →
      Γ ⊢ app f x ⇒ T [ ann x S ]
    t-ann : ∀{n} {Γ : ctx n} {x T T'} → (T ↝ T') → (Γ ⊢ T' ⇐ type) → (Γ ⊢ x ⇐ T') → Γ ⊢ ann x T ⇒ T'

progress-⇐ :
  ∀{n} {Γ : ctx n} {x T} →
  Γ ⊢ x ⇐ T →
  (∃[ x' ] (x ↓ x') ⊎ value x)
progress-⇐ t-type = inr value-type
progress-⇐ (t-lam x v x-T) = inr value-lam
progress-⇐ (t-pi S-type eval-refl v-S x-T) = inr (value-pi v-S)
progress-⇐ (t-pi {n} {Γ} {S} {S''} {T} _ (eval-trans {.n} {.S} {S'} S-S' _) _ _) =
  inl (pi S' T , step-pi S-S')
progress-⇐ (t-embed a b) = {!!}

progress-⇒ :
  ∀{n} {Γ : ctx n} {x T} →
  Γ ⊢ x ⇒ T →
  (∃[ x' ] (x ↓ x') ⊎ value x)
progress-⇒ (t-var x) = {!!}
progress-⇒ (t-app x-T x₁) = {!!}
progress-⇒ (t-ann x₁ x₂ x₃) = {!!}

strong-normalisation :
  ∀{n} {Γ : ctx n} {x T} →
  Γ ⊢ x ⇐ T →
  ∃[ x' ] (x ↝ x' × value x')
strong-normalisation = {!!}

preservation-⇐ :
  ∀{n} {Γ : ctx n} {x x' T} →
  Γ ⊢ x ⇐ T →
  x ↓ x' →
  Γ ⊢ x' ⇐ T
preservation-⇐ t-type ()
preservation-⇐ (t-lam S-S' v-S' x-T) ()
preservation-⇐ (t-pi S-S' v-S' x-T x-T₁) (step-pi x-x') = {!!}
preservation-⇐ (t-embed x₁ x₂) x-x' = {!!}
