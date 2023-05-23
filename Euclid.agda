module Euclid where

open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s; _≰_; _<_; _≤′_; ≤′-refl; ≤′-step; _!)
open import Data.Nat.Properties using (+-comm; 1+n≰n; n≮0; n<1+n; 1≤n!; ≰⇒≥; ≤-refl; ≤-trans; ≤⇒≤′)
open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Divisibility using (_∣_; _∤_; ∣-refl; ∣-trans; ∣1⇒≡1; ∣m+n∣m⇒∣n; ∣m∣n⇒∣m+n; m∣m*n; ∣n⇒∣m*n)
open import Data.Nat.Primality using (Prime; Composite; prime?; ¬prime⇒composite)
open import Data.Product using (_,_; ∃-syntax; _×_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym)
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

small-divisor-! : ∀ {k n} → 1 ≤ k → k ≤ n → k ∣ n !
small-divisor-! 1≤k k≤n = small-divisor′ 1≤k (≤⇒≤′ k≤n) where
  small-divisor′ : ∀ {k n} → 1 ≤ k → k ≤′ n → k ∣ n !
  small-divisor′ {0} {n} 1≤0 = ⊥-elim (1+n≰n 1≤0)
  small-divisor′ {suc k} _ ≤′-refl = m∣m*n (k !)
  small-divisor′ {suc k} {suc n} 1≤1+k (≤′-step 1+k≤n) = ∣m∣n⇒∣m+n  1+k∣n! (∣n⇒∣m*n n 1+k∣n!) where
    1+k∣n! : 1 + k ∣ n !
    1+k∣n! = small-divisor′ 1≤1+k 1+k≤n

large-divisor-! : ∀ {k n} → 2 ≤ k → k ∣ 1 + n ! → n ≤ k
large-divisor-! 2≤k k∣1+n! = ≰⇒≥ (large-divisor′ 2≤k k∣1+n!) where
  large-divisor′ : ∀ {k n} → 2 ≤ k → k ∣ 1 + n ! → k ≰ n
  large-divisor′ {k} {n} 2≤k k∣1+n! = qed where
    qed : k ≰ n
    qed k≤n = 1+n≰n contradiction where
      k∣n!+1 : k ∣ n ! + 1
      k∣n!+1 rewrite (+-comm 1 (n !)) = k∣1+n!
      k∣1 : k ∣ 1
      k∣1 = ∣m+n∣m⇒∣n k∣n!+1 (small-divisor-! (≤-trans (s≤s z≤n) 2≤k) k≤n)
      contradiction : 2 ≤ 1
      contradiction rewrite (sym (∣1⇒≡1 k∣1)) = 2≤k

prime≥2 : ∀ {n} → Prime n → 2 ≤ n
prime≥2 {0} p = ⊥-elim p
prime≥2 {1} p = ⊥-elim p
prime≥2 {suc (suc _)} _ = s≤s (s≤s z≤n)

infinite-primes : ∀ n → ∃[ k ] Prime k × n ≤ k
infinite-primes n = next-prime (prime-divisor (1 + n !) (s≤s (1≤n! n))) where
  next-prime : Has-Prime-Divisor (1 + n !) → ∃[ k ] Prime k × n ≤ k
  next-prime (p , (prime-p , p∣1+n!)) = (p , prime-p , large-divisor-! (prime≥2 prime-p) p∣1+n!)
