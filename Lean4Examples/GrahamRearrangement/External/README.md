# External proofs

This directory contains self-contained formalizations of results used by the
Pham--Sauermann development that originate outside the paper.

## Hypergeometric concentration

The paper cites Janson--Łuczak--Ruciński, *Random Graphs*, Theorem 2.10 and
Eq. (2.6), for a hypergeometric lower-tail estimate.  The project no longer
assumes that estimate as an axiom.

The proof hierarchy is:

- `Hypergeometric/Sampling.lean`
  - finite sequential sampling without replacement;
  - support/nodup invariants;
  - equivalence with uniform `powersetCard` sampling.
- `Hypergeometric/Hoeffding.lean`
  - centered exposure martingale;
  - bounded one-step drift;
  - finite Hoeffding exponential-moment bound;
  - generic lower tail for without-replacement sampling.
- `Hypergeometric/Tails.lean`
  - transfer to uniform fixed-cardinality subsets;
  - exact `exp (-k/32)` and `exp (-k/24)` estimates used in Lemmas 3.1 and 3.3.
- `Hypergeometric.lean`
  - umbrella import.

The analytic Hoeffding lemma itself is taken from mathlib as a proved theorem,
not as a project axiom.

## Trust boundary

There are no custom `axiom`, `sorry`, or `admit` declarations in this
external proof hierarchy.  Standard Lean/classical foundations and proved
mathlib theorems form the remaining trust base.
