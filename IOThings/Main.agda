{-# OPTIONS --without-K --guardedness #-}

module Main where

import IO.Primitive as Prim
import IO.Finite as Finite

open import Level
open import IO.Base
open import IO.Finite using (getLine; putStrLn)
open import Agda.Primitive
open import Agda.Builtin.Unit

ℓ₀ : Level
ℓ₀ = lzero

runTest : IO (Lift ℓ₀ ⊤)
runTest =
  putStrLn "memes irados"
  >> getLine
  >>= putStrLn

main : Main
main =
  run runTest
