# Euclid's Theorem in Agda

I was generally unsatisfied with the constructive proofs of [Euclid's Theorem](https://en.wikipedia.org/wiki/Euclid%27s_theorem) written in Agda I could find on the internet, so I decided to write my own.
The aim was for it to be simultaeously simple and pedagogically useful.
This meant taking advantage of the standard library as much as possible, but not in a way that obfuscated the nature of the proof.
The approach of the proof is the standard one: for a given number $n$, we find a prime divisor of $1 + n!$, which we can then prove must be greater than $n$.

There are two features of the proof that depend heavily on functions in the standard library, which are not obvious from the get-go.

1. Finding a prime divisor requires *strong* induction (`<-rec`) since it requires recursing on divisors, not predecessors. It is a straightforward exercise to prove the strong induction principle for $\mathbb N$ in Agda.

2. Proving that a non-prime number is composite (`¬prime⇒composite`) requires commuting negation with bounded quantification over decidable predicates.
   This is mildy tricky to do bespoke, but also a good exercise.
   


