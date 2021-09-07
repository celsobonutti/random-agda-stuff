module Vector where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc)
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open Eq.≡-Reasoning

data Vector (A : Set) : ℕ → Set where
  [] : Vector A 0
  _::_ : {size : ℕ} → A → Vector A size → Vector A (suc size)

infixr 5 _::_

empty : Vector ℕ 0
empty = []

test : Vector ℕ 5
test = 1 :: 2 :: 3 :: 4 :: 5 :: []

snoc : ∀ {size : ℕ} {A : Set} → A → Vector A size → Vector A (suc size)
snoc x [] = x :: []
snoc x (x₁ :: xs) = x₁ :: snoc x xs

invert : ∀ {size : ℕ} {A : Set} → Vector A size → Vector A size
invert [] = []
invert (x :: xs) = snoc x (invert xs)

invert-snoc : ∀ {size : ℕ} {A : Set} (x : A) (xs : Vector A size) →
              x :: invert (xs) ≡ invert (snoc x xs)
invert-snoc x [] = refl
invert-snoc x (y :: ys) =
  begin
    x :: invert (y :: ys)
  ≡⟨⟩
    x :: snoc y (invert ys)
  ≡⟨ cong (snoc y) (invert-snoc x ys) ⟩
    snoc y (invert (snoc x ys))
  ∎


invert-invert : ∀ {size : ℕ} {A : Set} (xs : Vector A size) → invert (invert xs) ≡ xs
invert-invert [] = refl
invert-invert (x :: xs) =
  begin
    invert (invert (x :: xs))
  ≡⟨⟩
    invert (snoc x (invert xs))
  ≡⟨ sym(invert-snoc x (invert xs)) ⟩
    x :: invert (invert xs)
  ≡⟨ cong (x ::_) (invert-invert xs) ⟩
    x :: xs
  ∎

