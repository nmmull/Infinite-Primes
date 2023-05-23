module Euclid where

open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; _≤′_; z≤n; s≤s; ≤′-refl; ≤′-step; _≤?_; _!)
open import Data.Nat.Properties using (1+n≰n; n≮0; n<1+n; ≤⇒≤′; ≤-refl; allUpTo?)
open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Divisibility using (_∣_; _∤_; _∣?_; ∣-refl; ∣-trans)
open import Data.Nat.Primality using (Prime; Composite; prime?; ¬prime⇒composite)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_)
import Relation.Unary as U

Has-Prime-Divisor : ℕ → Set
Has-Prime-Divisor n = ∃[ k ] Prime k × k ∣ n

prime-divisor : ∀ n → 2 ≤ n → Has-Prime-Divisor n
prime-divisor 1 2≤1 = ⊥-elim (1+n≰n 2≤1)
prime-divisor (suc (suc n)) _ = <-rec _ go n where
  go : ∀ k → (∀ i → i < k → Has-Prime-Divisor (2 + i)) → Has-Prime-Divisor (2 + k)
  go k strong-ih with prime? (2 + k)
  go k strong-ih | yes prime-2+k = (2 + k , prime-2+k , ∣-refl)
  go k strong-ih | no ¬prime-2+k = composite⇒prime-divisor (¬prime⇒composite (s≤s (s≤s z≤n)) ¬prime-2+k) where
    strong-ih′ : ∀ i → 2 ≤ i → i < 2 + k → Has-Prime-Divisor i
    strong-ih′ 1 2≤1 = ⊥-elim (1+n≰n 2≤1)
    strong-ih′ (suc (suc i)) _ (s≤s (s≤s i<k)) = strong-ih i i<k
    composite⇒prime-divisor : Composite (2 + k) → Has-Prime-Divisor (2 + k)
    composite⇒prime-divisor (d , (2≤d , (d<2+k , d∣2+k))) = prime-divisor-d⇒prime-divisor-2+k (strong-ih′ d 2≤d d<2+k)  where
      prime-divisor-d⇒prime-divisor-2+k : Has-Prime-Divisor d → Has-Prime-Divisor (2 + k)
      prime-divisor-d⇒prime-divisor-2+k (p , (prime-p , p∣d)) = (p , prime-p , ∣-trans p∣d d∣2+k)

large-divisor : ∀ {n k} → k ∣ 1 + n ! → n ≤ k
large-divisor = {!!}

infinite-primes : ∀ n → ∃[ k ] Prime k × n ≤ k
infinite-primes = {!!}
  
  
