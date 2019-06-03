module TT where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _,_; proj₁)

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

infixl 5 _∷_
data ctx : ℕ → Set where
  ◆ : ctx 0
  _∷_ : ∀{n} → ctx n → tt check n → ctx (suc n)

ρ : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ρ f zero = zero
ρ f (suc n) = suc (f n)

rename : ∀{s m n} → (Fin m → Fin n) → tt s m → tt s n
rename f (var x) = var (f x)
rename f (app t t₁) = app (rename f t) (rename f t₁)
rename f (ann t t₁) = ann (rename f t) (rename f t₁)
rename f (lam t) = lam (rename (ρ f) t)
rename f (pi t t₁) = pi (rename f t) (rename (ρ f) t₁)
rename f type = type
rename f (embed t) = embed (rename f t)

data Rename-Ctx : ∀{m n} → (Fin m → Fin n) → ctx m → ctx n → Set where
  Id : ∀{n} {Γ} → Rename-Ctx (λ x → x) Γ Γ
  Skip :
    ∀{m n} {f : Fin m → Fin n} {Γ Γ'} {S} →
    Rename-Ctx f Γ Γ' →
    Rename-Ctx (λ x → suc (f x)) Γ (Γ' ∷ S)
  Go :
    ∀{n} {f : Fin n → Fin n} {Γ Γ'} {S} →
    Rename-Ctx f Γ Γ' →
    Rename-Ctx (ρ f) (Γ ∷ S) (Γ' ∷ rename f S)

σ : ∀{m n} → (Fin m → tt infer n) → Fin (suc m) → tt infer (suc n)
σ f zero = var zero
σ f (suc n) = rename suc (f n)

subst : ∀{s m n} → (Fin m → tt infer n) → tt s m → tt s n
subst f (var x) = f x
subst f (app t t₁) = app (subst f t) (subst f t₁)
subst f (ann t t₁) = ann (subst f t) (subst f t₁)
subst f (lam t) = lam (subst (σ f) t)
subst f (pi t t₁) = pi (subst f t) (subst (σ f) t₁)
subst f type = type
subst f (embed t) = embed (subst f t)

infixl 5 _[_]
_[_] : ∀{s n} → tt s (suc n) → tt infer n → tt s n
a [ b ] = subst (λ{ zero → b; (suc n) → var n }) a

data lookup : ∀{n} → Fin n → ctx n → tt check n → Set where
  here : ∀{n} {rest : ctx n} {ty} → lookup zero (rest ∷ ty) (rename suc ty)
  there :
    ∀{n} {ix : Fin n} {rest} {ty ty'} →
    lookup ix rest ty →
    lookup (suc ix) (rest ∷ ty') (rename suc ty)

infix 4 _⊢_∶_
data _⊢_∶_ : ∀{s n} → ctx n → tt s n → tt check n → Set where
  t-var : ∀{n} {Γ : ctx n} {ix ty} → lookup ix Γ ty → Γ ⊢ var ix ∶ ty
  t-app :
    ∀{n} {Γ : ctx n} {f x} {S T} →
    Γ ⊢ f ∶ pi S T →
    Γ ⊢ x ∶ S →
    Γ ⊢ app f x ∶ T [ ann x S ]
  t-ann :
    ∀{n} {Γ : ctx  n} {x} {T} →
    Γ ⊢ x ∶ T →
    Γ ⊢ ann x T ∶ T
  t-lam :
    ∀{n} {Γ : ctx  n} {e} {S T} →
    Γ ∷ S ⊢ e ∶ T →
    Γ ⊢ lam e ∶ pi S T
  t-pi :
    ∀{n} {Γ : ctx n} {S T} →
    Γ ∷ S ⊢ T ∶ type →
    Γ ⊢ pi S T ∶ type
  t-type :
    ∀{n} {Γ : ctx n} →
    Γ ⊢ type ∶ type
  t-embed :
    ∀{n} {Γ : ctx n} {e} {S T} →
    S ≡ T →
    Γ ⊢ e ∶ S →
    Γ ⊢ embed e ∶ T

ρ-id : ρ (λ x → x) ≡ (λ x → x)
ρ-id = {!!}

rename-id : ∀{s n} (a : tt s n) → rename (λ x → x) a ≡ a
rename-id (var x) = refl
rename-id (app a b) rewrite rename-id a | rename-id b = refl
rename-id (ann a b) rewrite rename-id a | rename-id b = refl
rename-id (lam a) = {!!}
rename-id (pi a a₁) = {!!}
rename-id type = {!!}
rename-id (embed a) = {!!}

rename-lookup :
  ∀{m n} {f : Fin m → Fin n} {Γ Δ} {ix : Fin m} {T} →
  Rename-Ctx f Γ Δ →
  lookup ix Γ T →
  lookup (f ix) Δ (rename f T)
rename-lookup Id lkp = {!!}
rename-lookup (Skip rn) lkp = {!!}
rename-lookup (Go rn) lkp = {!!}

rename-correct :
  ∀{m n} {f : Fin m → Fin n} {Γ Δ} {s} {x : tt s m} {T} →
  Rename-Ctx f Γ Δ →
  Γ ⊢ x ∶ T →
  Δ ⊢ rename f x ∶ rename f T
rename-correct rn (t-var x) = t-var {!!}
rename-correct rn (t-app deriv deriv₁) = {!!}
rename-correct rn (t-ann deriv) = {!!}
rename-correct rn (t-lam deriv) = {!!}
rename-correct rn (t-pi deriv) = {!!}
rename-correct rn t-type = {!!}
rename-correct rn (t-embed x deriv) = {!!}
