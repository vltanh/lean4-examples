# Gradient-flow paper formalization status

Target: Nguyen–Montúfar, *On Parameter Symmetries and Conservation Laws in Gradient Flow* (arXiv:2609.34549v1).

## Current branch state

- Single Lean source: `Lean4Examples/gradient-flow-symmetries.lean`.
- No occurrences of `sorry`, `admit`, or custom `axiom` declarations.
- The source is intentionally uncompiled. Proof scripts still need elaboration/API repair against this repository's Lean 4.26 / mathlib 4.26 pin.
- Proposition 19 now uses an explicit `GenericPoint` predicate rather than the earlier `GenericWitnessAt` regular-rank surrogate.
- The chosen generic locus is the set where every hidden bias is nonzero; the source states and proves that this locus is open and dense and uses it only for the two roles genericity plays in Appendix G.2: a local diagonal-scaling slice and linear independence of the scaling generators.

## External mathematical inputs used by the paper

The paper itself invokes several results rather than reproving them. The Lean draft keeps these as named interfaces to be connected to formal libraries or vendored formalizations during compilation repair:

1. Submersion/local factorization theorem used in Proposition 4.
2. Maximal smooth local-flow existence and uniqueness.
3. Poincaré lemma on star-shaped domains.
4. Frobenius theorem.
5. Full-rank matrix-factorization uniqueness (Piziak–Odell).
6. Matrix-factorization conservation-law completeness from Marcotte et al. (2023), Lemma 28 in the paper.
7. Attention-head identifiability from Tran et al. (2025a), Theorem 27 in the paper.
8. Spectral theorem / positive matrix square roots and polar decomposition used in Lemma 29.

These are distinguished from the paper's own inheritance, attention, polynomial-network, and deep-linear arguments.

## Next repair pass

The next pass should eliminate provisional interface names for results proved inside the paper, then map the genuinely external inputs above to concrete library declarations or vendored proofs. Compilation can then be used only for API/typing repair; it should not reintroduce mathematical assumptions.
