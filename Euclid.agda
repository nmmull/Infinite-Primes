module Euclid where

open import Data.Nat using (ℕ; suc; _+_; _≤_; _≰_; _<_; _≤′_; z≤n; s≤s; ≤′-refl; ≤′-step; _≤?_; _!)
open import Data.Nat.Properties using (1+n≰n; n≮0; n<1+n; 1≤n!; ≤⇒≤′; ≰⇒≥; ≤-refl; allUpTo?)
open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Divisibility using (_∣_; _∤_; _∣?_; ∣-refl; ∣-trans; m∣m*n)
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

large-divisor : ∀ {n k} → 2 ≤ k → k ∣ 1 + n ! → n ≤ k
large-divisor {n} {k} 2≤k k∣1+n! = {!≰⇒≥ ?!} where
  small-divisor : ∀ {k} → 1 ≤ k → k ≤′ n → k ∣ n !
  small-divisor {0} 1≤0 = ⊥-elim (1+n≰n 1≤0)
  small-divisor {suc k} _ ≤′-refl = m∣m*n (k !)
  small-divisor {suc k} 1≤1+k (≤′-step 1+k≤p) = {!small-divisor !}
  l : k ≤ n → k ∣ 1
  l k≤n = {!small-divisor ? (≤⇒≤′ k≤n) !}
  lemma : k ≰ n
  lemma k≤n = {!!}

prime≥2 : ∀ {n} → Prime n → 2 ≤ n
prime≥2 {0} p = ⊥-elim p
prime≥2 {1} p = ⊥-elim p
prime≥2 {suc (suc _)} _ = s≤s (s≤s z≤n)

infinite-primes : ∀ n → ∃[ k ] Prime k × n ≤ k
infinite-primes n = next-prime (prime-divisor (1 + n !) (s≤s (1≤n! n))) where
  next-prime : Has-Prime-Divisor (1 + n !) → ∃[ k ] Prime k × n ≤ k
  next-prime (p , (prime-p , p∣1+n!)) = (p , prime-p , large-divisor (prime≥2 prime-p) p∣1+n!)
  
