# Graham rearrangement formalization checklist

Paper: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture* (arXiv:2602.15797).

- [ ] Define valid orderings and the partial-sum formulation in finite cyclic groups.
- [ ] Formalize the elementary norm estimates from Section 2 (Facts 2.1--2.3).
- [ ] Connect the finite cyclic-group norm to the Fourier-character estimate (Fact 2.5).
- [ ] Record the Cauchy--Davenport consequence used as Fact 2.4.
- [ ] State the Boolean-slice anticoncentration theorem (Theorem 1.3) in Lean-friendly finite-probability language.
- [ ] State the large-slice corollary (Corollary 1.4) and the chain anticoncentration input from Section 4.
- [ ] Formalize the combinatorial notion of zero-sum segments in an ordering.
- [ ] Formalize the local-repair/endpoint-swap setup from Section 5.
- [ ] State the main theorem (Theorem 1.2) in terms of a finite field/cyclic group of prime order.
- [ ] Discharge the elementary lemmas without `sorry`; isolate any remaining deep probabilistic inputs explicitly.
- [ ] Build the file with the repository's Lean 4.26 / mathlib v4.26.0 toolchain.
- [ ] Document exactly which parts of the paper are proved versus assumed in the PR description.
