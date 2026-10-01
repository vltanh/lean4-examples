# Graham rearrangement formalization checklist

Paper: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture* (arXiv:2602.15797).

- [x] Define valid orderings and the partial-sum formulation in finite cyclic groups.
- [x] Formalize the Section 2 interfaces (Facts 2.1--2.5), including the cyclic norm and Cauchy--Davenport consequence.
- [x] State the Boolean-slice anticoncentration theorem (Theorem 1.3) in finite-cardinality probability language.
- [x] State the large-slice corollary (Corollary 1.4).
- [x] Formalize nested-chain sample spaces and state Corollary 4.2.
- [x] Formalize zero-sum segments and bad right endpoints.
- [x] Formalize admissible local swaps, blocked choices, and bad events B1/B2/B3 from Section 5.
- [x] State the deterministic Section 5 repair step.
- [x] State the main theorem (Theorem 1.2) in terms of `ZMod p`.
- [x] Encode the final dependency from the Section 5 bad-event bounds to Theorem 1.2.
- [x] Isolate the deep analytic/probabilistic and long counting arguments explicitly with `sorry`.
- [x] Document the admitted/proved boundary in the PR description.

Per request, this branch has no CI workflow and no compilation is performed as part of this work.
