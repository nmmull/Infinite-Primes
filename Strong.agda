module Strong where

open import Data.Nat using (ℕ; suc; s≤s; z≤n; _≤_; _<_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≮0; ≤⇒≤′; ≤-refl)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (yes; no; ¬?; _→-dec_)
open import Relation.Nullary.Negation using (¬_)
import Relation.Unary as U

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
