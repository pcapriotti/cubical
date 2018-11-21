{-# OPTIONS --cubical #-}

module Cubical.Basics.Squid where

open import Cubical.Core.Primitives
open import Cubical.Core.Everything

open import Cubical.Basics.Int

_·_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_·_ = compPath

data ℤ : Set where
  zero : ℤ
  suc : ℤ → ℤ
  pred : ℤ → ℤ
  suc-pred : (n : ℤ) → suc (pred n) ≡ n
  pred' : ℤ → ℤ
  pred'-suc : (n : ℤ) → pred' (suc n) ≡ n

record isBiInv {A B : Set}(f : A → B) : Set where
  field
    g : B → A
    inv : (b : B) → f (g b) ≡ b
    g' : B → A
    inv' : (a : A) → g' (f a) ≡ a

record ℤ-Alg (A : Set) : Set where
  field
    z : A
    s : A → A
    e : isBiInv s

  open isBiInv e public renaming
    ( g to p
    ; inv to α
    ; g' to p'
    ; inv' to α' )

module _ {A₀ B₀ : Set} (A : ℤ-Alg A₀) (B : ℤ-Alg B₀) (f : A₀ → B₀) where
  open ℤ-Alg

  -- "partial" algebra morphism
  record ℤ-Alg-Mor : Set where
    field
      z₁ : f (z A) ≡ z B
      s₁ : (a : A₀) → f (s A a) ≡ s B (f a)

  -- algebra morphism
  record ℤ-Alg-Mor' : Set where
    field
      z₁ : f (z A) ≡ z B
      s₁ : {a : A₀}{b : B₀} → f a ≡ b → f (s A a) ≡ s B b
      p₁ : {a : A₀}{b : B₀} → f a ≡ b → f (p A a) ≡ p B b
      α₁ : {a : A₀}{b : B₀}(q : f a ≡ b)
         → PathP (λ i → f (α A a i) ≡ α B b i) (s₁ (p₁ q)) q

      p₁' : {a : A₀}{b : B₀} → f a ≡ b → f (p' A a) ≡ p' B b
      α₁' : {a : A₀}{b : B₀}(q : f a ≡ b)
          → PathP (λ i → f (α' A a i) ≡ α' B b i) (p₁' (s₁ q)) q

  mor' : ℤ-Alg-Mor → ℤ-Alg-Mor'
  mor' m = record
    { z₁ = pz₁ m
    ; s₁ = s₁
    ; p₁ = p₁
    ; α₁ = α₁
    ; p₁' = p₁'
    ; α₁' = α₁' }
    where
      open ℤ-Alg-Mor renaming (z₁ to pz₁; s₁ to ps₁)

      s₁ : {a : A₀}{b : B₀} → f a ≡ b → f (s A a) ≡ s B b
      s₁ {a} q = ps₁ m a · λ i → s B (q i)

      p₁ : {a : A₀}{b : B₀} → f a ≡ b → f (p A a) ≡ p B b
      p₁ = {!!}

      α₁ : {a : A₀}{b : B₀}(q : f a ≡ b)
         → PathP (λ i → f (α A a i) ≡ α B b i) (s₁ (p₁ q)) q
      α₁ = {!!}

      p₁' : {a : A₀}{b : B₀} → f a ≡ b → f (p' A a) ≡ p' B b
      p₁' = {!!}

      α₁' : {a : A₀}{b : B₀}(q : f a ≡ b)
          → PathP (λ i → f (α' A a i) ≡ α' B b i) (p₁' (s₁ q)) q
      α₁' = {!!}

module _ {A₀ B₀ C₀ : Set} (A : ℤ-Alg A₀) (B : ℤ-Alg B₀) (C : ℤ-Alg C₀)
         {f : A₀ → B₀} {g : B₀ → C₀}
         (mf : ℤ-Alg-Mor A B f)
         (mg : ℤ-Alg-Mor B C g) where
  comp-mor : ℤ-Alg-Mor A C (λ a → g (f a))
  comp-mor = {!!}

id-mor : {A₀ : Set} (A : ℤ-Alg A₀) → ℤ-Alg-Mor A A (λ a → a)
id-mor A = record
  { z₁ = refl
  ; s₁ = λ a → refl }

-- initiality

Z : ℤ-Alg ℤ
Z = record
  { z = zero
  ; s = suc
  ; e = record
    { g = pred
    ; inv = suc-pred
    ; g' = pred'
    ; inv' = pred'-suc } }

module _ {A₀ : Set} (A : ℤ-Alg A₀) where
  open ℤ-Alg

  ! : ℤ → A₀
  ! zero = z A
  ! (suc n) = s A (! n)
  ! (pred n) = p A (! n)
  ! (suc-pred n i) = α A (! n) i
  ! (pred' n) = p' A (! n)
  ! (pred'-suc n i) = α' A (! n) i

  !-mor : ℤ-Alg-Mor Z A !
  !-mor = record
    { z₁ = refl
    ; s₁ = λ a → refl }

  module _ {f : ℤ → A₀} (mf : ℤ-Alg-Mor Z A f) where
    open ℤ-Alg-Mor'
    mf' = mor' Z A f mf

    uniq₀ : (n : ℤ) → f n ≡ ! n
    uniq₀ zero = z₁ mf'
    uniq₀ (suc n) = s₁ mf' (uniq₀ n)
    uniq₀ (pred n) = p₁ mf' (uniq₀ n)
    uniq₀ (suc-pred n i) = α₁ mf' (uniq₀ n) i
    uniq₀ (pred' n) = p₁' mf' (uniq₀ n)
    uniq₀ (pred'-suc n i) = α₁' mf' (uniq₀ n) i

  module _ {f g : ℤ → A₀} (mf : ℤ-Alg-Mor Z A f) (mg : ℤ-Alg-Mor Z A g) where
    uniq : (n : ℤ) → f n ≡ g n
    uniq n = uniq₀ mf n · sym (uniq₀ mg n)

-- squid

aInt : ℤ-Alg Int
aInt = record
  { z = pos 0
  ; s = sucInt
  ; e = record
    { g = predInt
    ; inv = sucPred
    ; g' = predInt
    ; inv' = predSuc } }

module ℤ-Int where
  f : ℤ → Int
  f = ! aInt

  f-mor : ℤ-Alg-Mor Z aInt f
  f-mor = !-mor aInt

  g+ : ℕ → ℤ
  g+ zero = zero
  g+ (suc n) = suc (g+ n)

  g- : ℕ → ℤ
  g- zero = pred zero
  g- (suc n) = pred (g- n)

  g : Int → ℤ
  g (pos n) = g+ n
  g (negsuc n) = g- n

  α+ : (n : ℕ) → f (g+ n) ≡ pos n
  α+ zero = refl
  α+ (suc n) i = sucInt (α+ n i)

  α- : (n : ℕ) → f (g- n) ≡ negsuc n
  α- zero i = negsuc zero
  α- (suc n) i = predInt (α- n i)

  α : (n : Int) → f (g n) ≡ n
  α (pos n) = α+ n
  α (negsuc n) = α- n

  g-mor : ℤ-Alg-Mor aInt Z g
  g-mor = record
    { z₁ = refl
    ; s₁ = lem }
    where
      lem : ∀ n → g (sucInt n) ≡ suc (g n)
      lem (pos n) = refl
      lem (negsuc zero) = sym (suc-pred zero)
      lem (negsuc (suc n)) = sym (suc-pred (g- n))

  β : (n : ℤ) → g (f n) ≡ n
  β = uniq Z (comp-mor Z aInt Z f-mor g-mor) (id-mor Z)
