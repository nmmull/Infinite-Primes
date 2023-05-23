module Euclid where

open import Data.Nat using (ℕ; suc; _≤_; _<_; _≤′_; s≤s; ≤′-refl; ≤′-step; _≤?_)
open import Data.Nat.Properties using (1+n≰n; n≮0; n<1+n; ≤⇒≤′; ≤-refl; allUpTo?)
open import Data.Nat.Divisibility using (_∣_; _∤_; _∣?_; ∣-refl)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (yes; no; ¬?; _→-dec_)
open import Relation.Nullary.Negation using (¬_)
import Relation.Unary as U

Prime : ℕ → Set
Prime 0 = ⊥
Prime 1 = ⊥
Prime (suc (suc n)) = ∀ {k} → k < n → 2 ≤ k → k ∤ n

prime? : U.Decidable Prime
prime? 0 = no λ ()
prime? 1 = no λ ()
prime? (suc (suc n)) = allUpTo? (λ k → (2 ≤? k) →-dec ¬? (k ∣? n)) n

Composite : ℕ → Set
Composite 0 = ⊥
Composite 1 = ⊥
Composite (suc (suc n)) = ∃[ k ] (k < n) × (2 ≤ k) × (k ∣ n)

Has-Prime-Divisor : ℕ → Set
Has-Prime-Divisor n = ∃[ k ] Prime k × k ∣ n

ℕ-strong-ind : ∀ (P : ℕ → Set) → (∀ {k} → (∀ {i} → i < k → P i) → P k) → ∀ {n} → P n
ℕ-strong-ind P ih = pn′ ≤′-refl where
  P′ : ℕ → Set
  P′ i = ∀ {k} → k ≤′ i → P k
  p0′ : P′ 0
  p0′ {0} _ =  ih {0} λ {i} i<0 → ⊥-elim (n≮0 i<0)
  pn′ : ∀ {n} → P′ n
  pn′ {0} = p0′
  pn′ {suc i} ≤′-refl = ih help where
    help : ∀ {j} → suc j ≤ suc i → P j
    help (s≤s j≤i) = pn′ (≤⇒≤′ j≤i)
  pn′ {suc n} (≤′-step k≤n) = pn′ k≤n

¬∀⇒∃¬ : ∀ {n} {P : ℕ → Set} → U.Decidable P → ¬ (∀ {i} → i < n → P i) → ∃[ i ] i < n × ¬ (P i)
¬∀⇒∃¬ {0} p? ¬∀ = ⊥-elim (¬∀ (λ i<0 → ⊥-elim (n≮0 i<0)))
¬∀⇒∃¬ {suc n} {P} p? ¬∀ with p? n
... | yes pn = l2 (¬∀⇒∃¬ {n} p? (λ prf → l1 (l0 prf))) where
  l0 : (∀ {i} → i < n → P i) → ∀ {i} → suc i ≤′ n → P i
  l0 = {!!}
  l1 : ¬ (∀ {i} → (suc i) ≤′ n → P i)
  l1 ∀i<n =  ¬∀ (λ i<n → l3 (≤⇒≤′ i<n)) where
    l3 : ∀ {i} → suc i ≤′ suc n → P i
    l3 ≤′-refl = pn
    l3 (≤′-step si<n) = ∀i<n si<n
  l2 : ∃[ i ] i < n × ¬ (P i) → ∃[ i ] i < (suc n) × ¬ (P i)
  l2 = {!!}
... | no ¬pn = (n , ≤-refl , ¬pn)



--prime-divisor : ∀ n → 2 ≤ n → Has-Prime-Divisor n
--prime-divisor 1 2≤1 = ⊥-elim (1+n≰n 2≤1)
--prime-divisor (suc (suc n)) _ = ℕ-strong-ind (λ i → Has-Prime-Divisor (suc (suc i))) go n where
--  go : ∀ k → (∀ i → i < k → Has-Prime-Divisor (suc (suc i))) → Has-Prime-Divisor (suc (suc k))
--  go k prf with prime? (suc (suc k))
--  go k prf | yes prime-2+k = (suc (suc k) , {!!} , ∣-refl)
--  go k prf | no ¬prime-2+k = {!!} where
--    comp-2+k : Composite (suc (suc k))
--    comp-2+k = {!!}
    
