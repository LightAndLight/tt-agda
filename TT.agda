module TT where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Maybe using (Maybe; just; map)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

data value (n : ℕ) : (s : sort) → tt s n → Set where
  value-var : ∀{ix} → value n infer (var ix)
  -- if we allow variables to be values, then
  -- applications must also be values
  value-app :
    ∀{f x} →
    value n infer f →
    value n check x →
    (∃[ x ] (∃[ T ] (ann x T ≡ f)) → ⊥) →
    value n infer (app f x)
  value-ann :
    ∀{x T} →
    value n check x →
    value n check T →
    (∃[ e ] (embed e ≡ x) → ⊥) →
    value n infer (ann x T)
  value-lam :
    ∀{e} →
    value (suc n) check e →
    value n check (lam e)
  value-pi :
    ∀{S T} →
    value n check S →
    value (suc n) check T →
    value n check (pi S T)
  value-type : value n check type
  value-embed :
    ∀{e} →
    value n infer e →
    (∃[ x ] (∃[ T ] (ann x T ≡ e)) → ⊥) →
    value n check (embed e)

data _↓_ {n : ℕ} : {s : sort} → tt s n → tt s n → Set where
  step-app1 :
    ∀{f f' : tt infer n} {x : tt check n} →
    f ↓ f' →
    app f x ↓ app f' x
  step-app2 :
    ∀{f : tt infer n} {x x' : tt check n} →
    value n infer f →
    x ↓ x' →
    app f x ↓ app f x'
  step-beta :
    ∀{e : tt check (suc n)} {x S : tt check n} {T : tt check (suc n)} →
    value n infer (ann (lam e) (pi S T)) →
    value n check x →
    app (ann (lam e) (pi S T)) x ↓ ann (e [ ann x S ]) (T [ ann x S ])
  step-upsilon1 :
    ∀{x T} →
    value n check x →
    value n check T →
    embed (ann x T) ↓ x
  step-upsilon2 :
    ∀{x T} →
    value n infer x →
    value n check T →
    ann (embed x) T ↓ x
  step-ann1 : ∀{x x' T : tt check n} → value n check T → x ↓ x' → ann x T ↓ ann x' T
  step-ann2 : ∀{x T T' : tt check n} → T ↓ T' → ann x T ↓ ann x T'

  step-lam : ∀{e e' : tt check (suc n)} → e ↓ e' → lam e ↓ lam e'
  step-pi1 : ∀{S S' : tt check n} {T} → S ↓ S' → pi S T ↓ pi S' T
  step-pi2 : ∀{S : tt check n} {T T'} → value n check S → T ↓ T' → pi S T ↓ pi S T'
  step-embed : ∀{x x' : tt infer n} → x ↓ x' → embed x ↓ embed x'

value-done : ∀{s n} {x x' : tt s n} → value n s x → x ↓ x' → ⊥
value-done value-var ()
value-done (value-lam x-v) (step-lam x-x') = value-done x-v x-x'
value-done (value-pi v-S v-T) (step-pi1 S-S') = value-done v-S S-S'
value-done (value-pi v-S v-T) (step-pi2 _ T-T') = value-done v-T T-T'
value-done value-type ()
value-done (value-embed value-var not-ann) (step-embed x-x') = value-done value-var x-x'
value-done (value-embed (value-app v-f v-x not-ann') not-ann) (step-embed x-x') =
  value-done (value-app v-f v-x not-ann') x-x'
value-done (value-embed (value-ann v-x v-T not-embed) not-ann) x-x' = ⊥-elim (not-ann (_ , _ , refl))
value-done (value-app v-f v-x not-ann) (step-app1 x-x') = value-done v-f x-x'
value-done (value-app v-f v-x not-ann) (step-app2 _ x-x') = value-done v-x x-x'
value-done (value-app (value-ann v-f v-f₁ not-embed) v-x not-ann) (step-beta _ _) =
  ⊥-elim (not-ann (_ , (_ , refl)))
value-done (value-ann v-x v-T not-embed) (step-ann1 _ x-x') = value-done v-x x-x'
value-done (value-ann v-x v-T not-embed) (step-ann2 x-x') = value-done v-T x-x'
value-done (value-ann v-x v-T not-embed) (step-upsilon2 _ _) = ⊥-elim (not-embed (_ , refl))

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
    ∀{Γ : ctx n} {S T e} →
    (Γ ∷ S ⊢ e ∶ T) →
    Γ ⊢ lam e ∶ pi S T
  t-pi :
    ∀{Γ : ctx n} {S T} →
    (Γ ⊢ S ∶ type) →
    (Γ ∷ S ⊢ T ∶ type) →
    Γ ⊢ pi S T ∶ type
  t-embed : ∀{Γ : ctx n} {x T} → (Γ ⊢ x ∶ T) → Γ ⊢ embed x ∶ T

  t-var : ∀{ix Γ T} → index {n} ix Γ T → Γ ⊢ var ix ∶ T
  t-app :
    ∀{Γ : ctx n} {S T f x} →
    (Γ ⊢ f ∶ pi S T) →
    (Γ ⊢ x ∶ S) →
    Γ ⊢ app f x ∶ T [ ann x S ]
  t-ann :
    ∀{Γ : ctx n} {x T T'} →
    (Γ ⊢ T ∶ type) →
    (Γ ⊢ x ∶ T) →
    T ≡ T' →
    Γ ⊢ ann x T ∶ T'

subst-admissible-lam :
  ∀{sort n} {Γ : ctx n} {x : tt sort (suc (suc n))} {s S₁ S₂ T} →
  Γ ⊢ s ∶ S₁ →
  Γ ∷ S₁ ∷ S₂ ⊢ x ∶ T →
  Γ ∷ S₂ [ s ] ⊢ x [ s ] ∶ T [ s ]
subst-admissible-lam = ?

subst-admissible :
  ∀{sort n} {Γ : ctx n} {x : tt sort (suc n)} {s S T} →
  Γ ∷ S ⊢ x ∶ T →
  Γ ⊢ s ∶ S →
  Γ ⊢ x [ s ] ∶ T [ s ]
subst-admissible t-type s-S = t-type
subst-admissible (t-lam x-T) s-S = t-lam {!!}
subst-admissible (t-pi x-T x-T₁) s-S = {!!}
subst-admissible (t-embed x-T) s-S = {!!}
subst-admissible (t-var x) s-S = {!!}
subst-admissible (t-app x-T x-T₁) s-S = {!!}
subst-admissible (t-ann x-T x-T₁ x₁) s-S = {!!}

progress :
  ∀{s n} {Γ : ctx n} {x : tt s n} {T : tt check n} →
  Γ ⊢ x ∶ T →
  (Σ[ x' ∈ tt s n ] (x ↓ x') ⊎ value n s x)
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
progress (t-embed t) | inr value-var = inr (value-embed value-var (λ ()))
progress (t-embed t) | inr (value-ann v-x v-T not-embed) = inl (_ , step-upsilon1 v-x v-T)
progress (t-embed t) | inr (value-app value-var v-x not-ann) =
  inr (value-embed (value-app value-var v-x not-ann) (λ ()))
progress (t-embed t) | inr (value-app (value-app v-f v-f₁ not-ann') v-x not-ann) =
  inr (value-embed (value-app (value-app v-f v-f₁ not-ann') v-x not-ann) (λ ()))
progress (t-embed t) | inr (value-app (value-ann v-a v-T not-embed) v-x not-ann) =
  ⊥-elim (not-ann (_ , _ , refl))
progress (t-app f a) with progress f
progress (t-app f a) | inl (f' , f-f') = inl (_ , step-app1 f-f')
progress (t-app f a) | inr v-f with progress a
progress (t-app f a) | inr v-f | inl (x' , x-x') = inl (_ , step-app2 v-f x-x')
progress (t-app f a) | inr value-var | inr v-a = inr (value-app value-var v-a (λ ()))
progress (t-app f a) | inr (value-app v-f v-x not-ann) | inr v-a =
  inr (value-app (value-app v-f v-x not-ann) v-a (λ ()))
progress (t-app a x) | inr (value-ann (value-lam v-a) (value-lam v-T) not-embed) | inr v-x with a
progress (t-app a x)
  | inr (value-ann (value-lam v-a) (value-lam v-T) not-embed) | inr v-x | t-ann () _ _
progress (t-app a x) | inr (value-ann (value-lam v-a) value-type not-embed) | inr v-x with a
progress (t-app a x) | inr (value-ann (value-lam v-a) value-type not-embed) | inr v-x | t-ann _ _ ()
progress (t-app a x) | inr (value-ann (value-lam v-a) (value-embed v-T x₂) not-embed) | inr v-x with a
progress (t-app a x) | inr (value-ann (value-lam v-a) (value-embed v-T x₂) not-embed) | inr v-x | t-ann _ _ ()
progress (t-app (t-ann a () refl) x) | inr (value-ann (value-pi v-S v-T') v-T not-embed) | inr v-x
progress (t-app (t-ann f () refl) x) | inr (value-ann value-type v-T not-embed) | inr v-x
progress (t-app f x) | inr (value-ann (value-lam v-a) (value-pi v-S v-T) not-embed) | inr v-x =
  inl (_ , (step-beta (value-ann (value-lam v-a) (value-pi v-S v-T) not-embed) v-x))
progress (t-app f x) | inr (value-ann (value-embed v-a not-ann) v-T not-embed) | inr v-x =
  ⊥-elim (not-embed (_ , refl))
progress (t-ann x T T≡T') with progress x
progress (t-ann x T T≡T') | inl (x' , x-x') = inl (_ , step-ann2 x-x')
progress (t-ann x T T≡T') | inr v-x with progress T
progress (t-ann x T T≡T') | inr v-x | inl (T' , T-T') = inl (_ , step-ann1 v-x T-T')
progress (t-ann () T T≡T') | inr (value-lam v-x) | inr v-T
progress (t-ann (t-pi t-S t-T) T T≡T') | inr (value-pi v-S v-T) | inr (value-embed v-x x) =
  inl (_ , step-upsilon2 v-x (value-pi v-S v-T))
progress (t-ann (t-pi t-S t-T) () T≡T') | inr (value-pi v-S v-T) | inr (value-pi v-x v-x₁)
progress (t-ann (t-pi t-S t-T) () T≡T') | inr (value-pi v-S v-T) | inr value-type
progress (t-ann (t-pi t-S t-T) T T≡T') | inr (value-pi v-S v-T) | inr (value-lam v-x) =
  inr (value-ann (value-lam v-x) (value-pi v-S v-T) (λ ()))
progress (t-ann t-type () T≡T') | inr value-type | inr (value-lam v-T)
progress (t-ann t-type T T≡T') | inr value-type | inr (value-pi v-T v-T₁) =
  inr (value-ann (value-pi v-T v-T₁) value-type (λ ()))
progress (t-ann t-type T T≡T') | inr value-type | inr value-type =
  inr (value-ann value-type value-type (λ ()))
progress (t-ann t-type (t-embed T) T≡T') | inr value-type | inr (value-embed v-T not-ann) =
  inl (_ , step-upsilon2 v-T value-type)
progress (t-ann (t-embed x) () T≡T') | inr (value-embed v-x not-ann) | inr (value-lam v-T)
progress (t-ann (t-embed x) () T≡T') | inr (value-embed v-x not-ann) | inr (value-pi v-T v-T₁)
progress (t-ann x () T≡T') | inr (value-embed v-x not-ann) | inr value-type
progress (t-ann x T T≡T') | inr (value-embed v-x not-ann) | inr (value-embed v-T x₁) =
  inl (_ , step-upsilon2 v-T (value-embed v-x not-ann))

preservation-type :
  ∀{s n} {Γ : ctx n} {x : tt s n} {T T' : tt check n} →
  Γ ⊢ T ∶ type →
  Γ ⊢ x ∶ T →
  T ↓ T' →
  Γ ⊢ x ∶ T'
preservation-type T-type t-type ()
preservation-type (t-pi T-type T-type₁) (t-lam x-T) (step-pi1 T-T') = {!!}
preservation-type (t-pi T-type T-type₁) (t-lam x-T) (step-pi2 x T-T') = {!!}
preservation-type t-type (t-pi x-T x-T₁) ()
preservation-type t-type (t-embed x-T) ()
preservation-type (t-pi T-type T-type₁) (t-embed x-T) (step-pi1 T-T') = {!!}
preservation-type (t-pi T-type T-type₁) (t-embed x-T) (step-pi2 x₁ T-T') = {!!}
preservation-type (t-embed T-type) (t-embed x-T) (step-upsilon1 x₁ x₂) = {!!}
preservation-type (t-embed T-type) (t-embed x-T) (step-embed T-T') = {!!}
preservation-type t-type (t-var x) ()
preservation-type (t-pi T-type T-type₁) (t-var x) (step-pi1 T-T') = {!!}
preservation-type (t-pi T-type T-type₁) (t-var x) (step-pi2 x₁ T-T') = {!!}
preservation-type (t-embed T-type) (t-var x) (step-upsilon1 x₁ x₂) = {!!}
preservation-type (t-embed T-type) (t-var x) (step-embed T-T') = {!!}
preservation-type T-type (t-app x-T x-T₁) T-T' = {!!}
preservation-type T-type (t-ann x-T x-T₁ refl) T-T' = t-ann x-T x-T₁ {!!}

preservation :
  ∀{s n} {Γ : ctx n} {x x' : tt s n} {T : tt check n} →
  Γ ⊢ x ∶ T →
  x ↓ x' →
  Γ ⊢ x' ∶ T
preservation t-type ()
preservation (t-lam t) (step-lam x-x') = t-lam (preservation t x-x')
preservation (t-pi t t₁) (step-pi1 x-x') = t-pi (preservation t x-x') {!!}
preservation (t-pi t t₁) (step-pi2 x x-x') = t-pi t (preservation t₁ x-x')
preservation (t-embed t) (step-upsilon1 x x₁) with t
preservation (t-embed t) (step-upsilon1 x x₁) | t-ann _ ty refl = ty
preservation (t-embed t) (step-embed x-x') = t-embed (preservation t x-x')
preservation (t-var x) ()
preservation (t-app t-f t-x) (step-app1 f-f') = t-app (preservation t-f f-f') t-x
preservation (t-app t-f t-x) (step-app2 v-f x-x') =
  t-app {!!} (preservation t-x x-x')
preservation (t-app t t₁) (step-beta x₁ x₂) = {!!}
preservation (t-ann T t-type refl) (step-ann1 x ())
preservation (t-ann T t-type refl) (step-ann2 ())
preservation (t-ann T (t-lam x) refl) (step-ann1 x₁ x-x') =
  t-ann T (preservation (t-lam x) x-x') refl
preservation (t-ann T (t-lam x) refl) (step-ann2 x-x') = {!!}
preservation (t-ann T (t-pi x x₁) refl) x-x' = {!!}
preservation (t-ann T (t-embed x) refl) (step-upsilon2 _ _) = x
preservation (t-ann T (t-embed x) refl) (step-ann1 x₂ x-x') =
  t-ann T (preservation (t-embed x) x-x') refl
preservation (t-ann T (t-embed x) refl) (step-ann2 x-x') =
  {!!}

strong-normalisation :
  ∀{s n} {Γ : ctx n} {x : tt s n} {T : tt check n} →
  Γ ⊢ x ∶ T →
  Σ[ x' ∈ tt s n ] (x ↝ x' × value n s x')
strong-normalisation = {!!}
