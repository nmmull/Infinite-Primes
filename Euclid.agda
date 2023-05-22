module Euclid where

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Nat.Primality using (Prime)
open import Data.Nat.Divisibility using (_∣_)
open import Data.Product using (∃-syntax; _×_)

Has-Prime-Divisor : ℕ → Set
Has-Prime-Divisor n = ∃[ k ] Prime k × k ∣ n

prime-factor : ∀ n → 2 ≤ n → Has-Prime-Divisor n
prime-factor 1 2≤1 = {!1+n≰n !}
prime-factor (suc (suc n)) _ = ?
