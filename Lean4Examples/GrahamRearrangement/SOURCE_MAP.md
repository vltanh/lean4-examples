# Source map for the Pham--Sauermann formalization

Target: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture*,
arXiv:2602.15797v1.

This file maps the paper-facing Lean declarations to their location in the paper.
Pure implementation helpers are grouped with the result they support. The strict
axiom boundary contains only the two hypergeometric Chernoff specializations
explicitly cited by the paper from [8, Theorem 2.10 and Eq. (2.6)].

## Introduction

| Paper | Lean |
| --- | --- |
| valid ordering / partial sums | `Introduction.partialSums`, `IsOrdering`, `IsValidOrdering`, `HasValidOrdering` |
| Conjecture 1.1 | `Conjecture11Statement` |
| notation Σ(S) | `subsetSum` |
| Theorem 1.2 range | `InGrahamRange` and `Main.Theorem12Statement` |

## Section 2 — Preliminaries

| Paper | Lean |
| --- | --- |
| distance `||y||_Z` | `distToInt` |
| Fact 2.1 | `fact2_1`, `fact2_1_finset` |
| Fact 2.2 | `fact2_2` |
| `||x||_p` | `zmodNorm`, `cyclicDistance`, `cyclicDistance_eq_zmodNorm` |
| Fact 2.3 | `fact2_3`, `fact2_3_finset` |
| k-fold sumset | `kfoldSumset` |
| Fact 2.4 | `fact2_4` |
| `e_p` | `ep`, `ep_eq_stdAddChar` |
| Fact 2.5 | `fact2_5` |

Section 2 has no project axioms. Cauchy--Schwarz, Taylor/Lagrange remainder,
and Cauchy--Davenport are used through proved/library theorems, and Facts 2.1--2.5
follow the paper's internal proofs.

## Section 3 — Boolean-slice anticoncentration

### Sampling and deterministic quantities

| Paper object | Lean |
| --- | --- |
| uniform size-m subset mass | `BooleanSlice/Definitions.sliceMass` |
| balanced block sizes | `balancedBlockSize` |
| random balanced partitions | `IsBalancedPartition`, `balancedPartitions` |
| one choice per block | `blockChoices`, `choiceSet`, `choiceSum`, `conditionalSumMass` |
| partition expectation/probability | `partitionExpectation`, `partitionMass` |
| ψ(χ) | `psi` |
| Ψ(χ) | `Psi` |
| A₀, A_t | `A0`, `At` |
| B_t | `Bset` |
| D_t and centers | `Dset`, `centerAt`, `centerAt_spec` |
| J_{χ,t} | `Jset` |
| Q_{t,δ} | `Qset` |

### Fourier reduction

| Paper | Lean |
| --- | --- |
| (3.1) and block Fourier factorization | `conditional_sum_mass_le_exp_psi` |
| (3.2) | contained in `conditional_sum_mass_le_exp_psi` through the block-character decay bound |
| (3.3) | `psi_lower_bound` |
| ψ(0)=0 | `psi_zero` |
| ψ(χ)≤m | `psi_le_m` |
| dyadic decomposition | `dyadic_conditional_bound` |
| (3.4) | `equation_3_4` |

### Lemmas and theorem

| Paper | Lean |
| --- | --- |
| Lemma 3.1 | `lemma3_1` |
| Lemma 3.2 | `lemma3_2` |
| Lemma 3.3 | `lemma3_3` |
| Lemma 3.4 | `lemma3_4` |
| Lemma 3.5 | `lemma3_5` |
| Lemma 3.6 | `lemma3_6` |
| Lemma 3.7 | `lemma3_7` |
| Theorem 1.3 | `theorem13` |

`BooleanSlice/External.lean` is axiom-free. The only axiomatized Section 3
input is the hypergeometric Chernoff estimate explicitly cited as [8, Theorem
2.10 and Eq. (2.6)], specialized in the general `External.lean` file.

### Fidelity notes

1. Two transition sentences in the paper use `D_t \ B_{32t}`, while the
   numbered Lemmas 3.2/3.3 and the subsequent proof use `B_{2000t}`.
   The formalization follows the numbered statements and proof, i.e. `2000t`.
2. The balanced-partition prose contains a block-size wording inconsistency.
   The formalization uses the quotient/remainder partition intended by the
   argument: each block has size `floor(n/m)` or `floor(n/m)+1`, and exactly
   `n % m` labelled blocks have the larger size.
3. In the proof of Lemma 3.2 the PDF/HTML prints the bound
   `|S ∩ J_{χ,t}| · 265t/m`, but the next displayed line bounds four times
   this contribution by `1024t/m`. Since `J_{χ,t}` is defined by radius
   `16√(t/m)`, the direct squared bound is `256t/m`, and
   `4·256=1024`. The formalization uses `256`; reproducing the printed
   `265` would make the following inequality false.

## Section 4 — Combinatorial anticoncentration

| Paper | Lean |
| --- | --- |
| Lemma 4.1 | `Combinatorial/Lemma41.lemma4_1` |
| Corollary 1.4 | `Combinatorial/Corollary14.corollary14` |
| chain sample space | `chainFamily`, `chainMass`, `IsChainSizeTuple` |
| Corollary 4.2 | `Combinatorial/Corollary42.corollary42` |
| k=1 specialization used in Section 5 | `corollary42_one_bound` |
| kernel notation for Lemma 4.3 | `prefixKernelSum`, `omittedKernelSum`, `lemma43LHS`, `lemma43RHS` |
| equation (4.1) | `equation_4_1` |
| Lemma 4.3 | `lemma4_3` |

All finite-sampling/exposure statements in Section 4 are proved internally;
`Combinatorial/External.lean` contains no axioms.

## Section 5 — Rearrangement conjecture

### Indexing and zero-sum intervals

| Paper | Lean |
| --- | --- |
| paper positions 1,...,n | `paperPos : Fin n → Nat` |
| interval [a,b] | `indexInterval`, `indexedIntervalSum` |
| B(σ) | `badRightEndpoints` |
| valid-ordering/zero-segment equivalence | `valid_iff_noZeroPaperSegments` |
| indexed/list ordering bridge | `indexedToList_isOrdering`, `applyPositionPerm_isIndexedOrdering` |

### Section 5 parameters

| Paper | Lean |
| --- | --- |
| D=ceil(3/α) | `section5D` |
| αD≥3 and D≥7 | `alpha_mul_section5D_ge_three`, `section5D_ge_seven` |
| choice of C_α and all displayed lower bounds | `Section5Parameters`, `exists_section5Parameters` |
| theorem regime | `Section5Regime` |
| |S|/p≤|S|^{-α} | `section5_card_over_p` |
| chain-constant asymptotic bound | `section5_chainConstant_bound` |

### Local swaps and bad events

| Paper | Lean |
| --- | --- |
| admissible collection/permutation | `IsAdmissibleCollection`, `collectionPerm`, `IsAdmissiblePermutation` |
| blocked y | `IsBlockedAt`, `blockedCandidates` |
| B₁ | `BadEvent1` |
| B₂ | `BadEvent2` |
| B₃ | `BadEvent3` |
| B₀ | `BadEvent0` |
| failure of all three main bad events | `Section5Good` |

### Lemmas 5.1--5.6

| Paper | Lean |
| --- | --- |
| Lemma 5.1 | `Rearrangement/Lemma51.lemma5_1` |
| equation (5.1) | `Rearrangement/Lemma54.equation_5_1` |
| Lemma 5.4 | `Rearrangement/Lemma54.lemma5_4` |
| Lemma 5.2 | `Rearrangement/Lemma52.lemma5_2` |
| interesting permutations | `IsInterestingPermutation`, `interestingPermutations` |
| Lemma 5.5 | `Rearrangement/Lemma55.lemma5_5` |
| Lemma 5.6 | `Rearrangement/Lemma56.lemma5_6` |
| E₁/E₂ side events | `RightRepairEvent`, `LeftRepairEvent` |
| Lemma 5.3 | `Rearrangement/Lemma53.lemma5_3` |

The finite-bijection, conditioning, matching, reversal, counting, and finite-choice
infrastructure used in these arguments is proved internally.
`Rearrangement/External.lean` and `Rearrangement/Reversal.lean` contain no axioms.

### Final repair and Theorem 1.2

| Paper | Lean |
| --- | --- |
| descending greedy repair | `Rearrangement/Repair.section5_local_repair` |
| Lemmas 5.1--5.3 assembled | `section5_bad_event_bounds` |
| union bound produces a good ordering | `exists_section5_good_ordering` |
| reduction to α<1/2 | `theorem12_of_section5_bounds` with β=min(α,1/4) |
| Theorem 1.2 | `theorem12` |

## External axiom boundary

The strict boundary has exactly two axioms, both in `External.lean`:

- `hypergeom_quarter_lower_tail`, used in Lemma 3.1;
- `hypergeom_three_quarters_lower_tail`, used in Lemma 3.3.

Both are direct specializations of the hypergeometric Chernoff bound that the
paper explicitly cites as [8, Theorem 2.10 and Eq. (2.6)]. Reference [8] is
S. Janson, T. Łuczak, and A. Ruciński, *Random Graphs*, John Wiley & Sons, 2011.

No paper-internal argument is axiomatized. All other External modules are
axiom-free.
