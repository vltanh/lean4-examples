# Deep proof audit checklist

Paper: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture*,
arXiv:2602.15797v1.

This checklist supersedes the earlier source-complete checklist for mathematical
fidelity. The formalization is **not audit-complete** until every unchecked item
below is resolved.

## Audit rule

The approved axiom boundary is: genuinely external results may remain axioms.
An axiom is not acceptable merely because it is generic-looking. If it packages
an argument Pham--Sauermann prove in this paper, it must become an internal Lean
proof.

A clean final boundary should contain only genuinely standard/external inputs
such as Cauchy--Schwarz, a general Taylor theorem, Cauchy--Davenport, standard
Fourier orthogonality, Markov/union bounds if desired, and the cited
hypergeometric Chernoff estimate.

# A. Statement-fidelity audit

## Corrections already made during this audit

- [x] Make the Section 3 center y_chi independent of t, chosen from the
      smallest positive t with chi in D_t.
- [x] Define J_{chi,t} as a subset of all Z_p, not as a subset of S.
- [x] Fix the Section 3 exponential-tail helper so it applies to both the 64m
      denominator in Lemma 3.1 and the 48m denominator in Lemma 3.3.
- [x] Visually verify from the PDF that Lemma 3.2 uses the slack constant 265,
      and restore 265 in Lean.
- [x] Continue using B_{2000t} in Lemmas 3.2/3.3 and the final proof while
      documenting the earlier B_{32t} prose occurrences as a paper inconsistency.
- [x] Use quotient/remainder balanced block sizes: floor(|S|/m) or
      floor(|S|/m)+1, with exactly |S|-m floor(|S|/m) larger labelled blocks.

## Statement checks still required

- [ ] Re-read every displayed statement in Sections 2--5 and compare Lean
      quantifier order, strict/non-strict inequalities, positivity assumptions,
      and constants line by line.
- [ ] Verify every pointwise-in-z theorem is explicitly equivalent to the
      paper's max-z formulation where applicable.
- [ ] Verify the Fin n translation of every Section 5 interval endpoint.
- [ ] Verify the distinct-partial-sums equivalence for 2 <= a <= b <= |S|,
      and separately justify the a < b form using 0 notin S.
- [ ] Verify composition order is exactly sigma o pi o pi_{b,y}.
- [ ] Verify collectionPerm agrees with the paper's pi_P.
- [ ] Verify exact endpoint ranges in Lemmas 5.5 and 5.6.
- [ ] Verify exact E1/E2 definitions in Lemma 5.3.
- [ ] Recheck all constants in the Section 5 choice of C_alpha.

# B. Critical logical defects in the current axiom layer

- [ ] Delete or repair Section4External.finiteConditionalProductBound.
      Its current statement is false: marginal bounds P(E_i) <= b_i do not
      imply P(intersection E_i) <= product b_i without conditional or
      independence hypotheses.
- [ ] Replace Section5External.bad0_parameter_count.
      It currently bounds the cardinality of the entire universe
      Fin n x Finset(Fin n) x Finset(Fin n) by n * 2^(40D+2), which is false.
      The paper only counts the filtered triples with J,J' inside the 20D window.
- [ ] Audit every axiom whose conclusion contains paper-specific event structure
      or paper-specific constants.
- [ ] Remove dead/unused axioms after dependency cleanup.

# C. Section 2 missing internal proofs

## Fact 2.1

- [ ] Replace External.distToInt_triangle by the paper's nearest-integer and
      triangle-inequality argument.
- [ ] Prove equivalence between min(fract y, 1-fract y) and distance to Z.
- [ ] Keep only genuine Cauchy--Schwarz as external if desired.

## Fact 2.2

- [ ] Replace cosine_nearest_integer_reduction, cosine_taylor_lower, and
      cosine_taylor_upper as currently specialized.
- [ ] Prove periodicity and symmetry internally.
- [ ] Reduce to y in [0,1/2] and prove distance-to-Z equals y there.
- [ ] Use only a general Taylor/Lagrange theorem externally.
- [ ] Reproduce 2*pi^2 <= 20 and the fourth-order upper estimate yielding 2.

## Fact 2.3

- [ ] Prove the representative calculation from Fact 2.1 exactly as in the paper.
- [ ] Verify representative-independence of zmodNorm.

## Fact 2.4

- [x] fact2_4 is now proved by induction from two-set Cauchy--Davenport.
- [ ] Remove obsolete iterated Cauchy--Davenport helper axioms if any remain.
- [ ] Keep only ordinary Cauchy--Davenport external.

## Fact 2.5

- [ ] Reduce Fact 2.5 to Fact 2.2 and the character/cosine identity.
- [ ] Document any ZMod/AddCircle interface identities as library facts, not
      paper results.

# D. Section 3 missing internal proofs

## Balanced-partition probability model

- [ ] Prove balancedPartitions_nonempty.
- [ ] Prove exact block cardinalities and floor/ceiling bounds internally.
- [ ] Prove the sqrt(2)|S|/m block-size estimate used in (3.3).
- [ ] Prove the one-from-each-block experiment gives a uniform size-m subset;
      replace sliceMass_eq_partition_average.
- [ ] Prove the conditional law of S_{i(x)} minus {x}.
- [ ] Prove k >= |S|/(2m) for the conditional block size.

## Equation (3.1)

- [ ] Replace External.independent_block_fourier_bound.
- [ ] Prove the character indicator identity from Fourier orthogonality.
- [ ] Prove expectation factorization from independence.
- [ ] Take absolute values exactly as in (3.1).
- [ ] Keep only standard character orthogonality external.

## Equation (3.2)

- [ ] Replace block_character_decay.
- [ ] Expand the squared character average.
- [ ] Rewrite conjugates using e_p(-x).
- [ ] Apply Fact 2.5 termwise.
- [ ] Prove the square-root/exponential comparison.
- [ ] Multiply over blocks and identify psi.

## Equations (3.3) and (3.4)

- [ ] Internalize the block-size arithmetic in psi_lower_bound.
- [ ] Prove psi(chi) <= m from the paper's norm bound.
- [ ] Prove the dyadic cover A0,A1,A2,...
- [ ] Replace External.dyadic_exp_sum_bound by a finite sum proof.
- [ ] Prove (3.4) directly from partition expectation.

## Lemma 3.1

- [ ] Split block_sparse_tail into internal conditional-uniformity plus the
      genuinely external hypergeometric Chernoff estimate.
- [ ] Derive exp(-k/32) <= exp(-|S|/(64m)) internally.
- [ ] Prove row-energy double counting internally.
- [ ] Retain only the cited Janson--Luczak--Rucinski hypergeometric estimate
      as external.

## Lemmas 3.2 and 3.3

- [x] Use the paper's t-independent center.
- [x] Use J_{chi,t} subset Z_p.
- [x] Restore the PDF's 265 slack constant.
- [ ] Prove the exact 1024, 976, and 200 numerical chain internally.
- [ ] Split block_dense_tail into conditional uniformity plus external Chernoff.
- [ ] Prove the half-distance inequality internally.

## Lemma 3.5

- [ ] Prove pair_uniform_expectation as a finite double-sum identity.
- [ ] Prove exists_fiber_mass_ge_pair_mass by averaging.
- [ ] Keep only Markov external if desired.
- [ ] Prove injectivity of y -> y-y'.

## Lemma 3.6

- [ ] Replace symmetric_character_square_sum.
- [ ] Derive it from standard Fourier orthogonality.
- [ ] Reproduce 9/10, 81/100, and 4/5 internally.

## Lemma 3.7 and Lemma 3.4

- [ ] Ensure Lemma 3.7 depends only on Fact 2.3 and finite sums.
- [ ] Prove the floor estimate for k=floor(sqrt(m/(2000t))).
- [ ] Prove k Q_{t,10t/m} subset Q_{t,1/200}.
- [ ] Reproduce Cauchy--Davenport and the 4/5 cardinality estimate internally.

## Final Theorem 1.3 proof

- [ ] Replace External.weighted_dyadic_split; it is essentially the paper's
      final dyadic summation.
- [ ] Prove the split into small scales and the final 22 scales.
- [ ] Prove sum exp(l/2-2^l) <= 2 internally or from a general series lemma.
- [ ] Prove 22 exp(-m/2^22) <= 22/|S|^4.
- [ ] Reproduce 30022 <= 2^24.

# E. Section 4 missing internal proofs

## Lemma 4.1

- [ ] Replace uniformSubset_twoStage with a finite counting proof.
- [ ] Prove complement cardinality/nonemptiness from powerset membership.

## Corollary 1.4

- [ ] Replace uniformSubset_split by the paper's two-stage uniformity proof.
- [ ] Recheck all three m-regimes and threshold inequalities.
- [ ] Verify the small-ground-set constant implements the paper's finite
      exceptional range correctly.
- [ ] Recheck m2=floor(epsilon*10^-3|S|/log|S|).
- [ ] Reproduce coefficient 50 C epsilon^(-3/2).

## Corollary 4.2

- [ ] Replace uniformChain_sumProductBound; it packages the core proof.
- [ ] Prove the largest-gap pigeonhole result internally.
- [ ] Prove complement-chain conditional uniformity.
- [ ] Formalize the exact exposure order and every remaining ground set.
- [ ] Prove a correct sequential conditional product bound.
- [ ] Delete the false finiteConditionalProductBound.

## Lemma 4.3

- [ ] Replace prefixKernelSum_le_pow; it packages equation (4.1).
- [ ] Prove the h=0 empty-tuple case.
- [ ] Prove the induction step by summing over m_{h+1}.
- [ ] Replace omittedKernelSum_le_prefix_mul.
- [ ] Prove the reversal substitution m'_i=|S|-m_{k+1-i}.
- [ ] Keep the reciprocal-square-root sum external only if treated as a
      genuinely standard analytic inequality.

# F. Section 5 missing internal proofs

## Uniform random bijections and conditioning

- [ ] Prove indexedOrderings_nonempty.
- [ ] Prove fixedIndexSet_sumMass.
- [ ] Prove ordering_perm_invariant.
- [ ] Prove ordering_conditional_perm_invariant.
- [ ] Prove conditional_nested_images_chainMass.
- [ ] Prove conditional_index_family_sumMass_le_zmod.
- [ ] Prove event/fiber averaging lemmas from finite cardinality ratios.

## Lemma 5.1

- [ ] Replace endpoint_reindex_sum_le by an explicit injection/reindexing proof.
- [ ] Replace two_sided_interval_kernel_sum_le.
- [ ] Prove the late-endpoint count internally.
- [ ] Recheck (30D+1)*3|S|^(-alpha) <= 1/100.

## Equation (5.1) and Lemma 5.4

- [ ] Prove distinct_index_subset_sums_mass_le using an index in J symmetric-difference J'.
- [ ] Prove the conditional fixed-b estimate after exposing the 20D window.
- [ ] Fix bad0_parameter_count to count the actual filtered triples.
- [ ] Prove the count |S|*2^(40D+2).
- [ ] Reproduce 2^(40D+5)/|S|^alpha <= 1/100 internally.

## Lemma 5.2

- [ ] Replace dense_window_extract with the paper's minimal-b0 argument.
- [ ] Prove a1,...,aD are distinct from failure of B0.
- [ ] Prove aD < b0 from failure of B0.
- [ ] Replace exists_sorting_perm by elementary finite sorting.
- [ ] Replace conditional_prefix_chain_union_bound.
- [ ] Prove the remaining ground-set size |S|-20D-1.
- [ ] Replace half_ground_lemma43Base_le, two_neg_alpha_pow_le_cube, and
      chainUpperBound_sum_le_lemma43 by explicit arithmetic/reindexing.
- [ ] Prove the |S|(20D)^D parameter count.
- [ ] Reproduce (D+1)(40D)^D/|S|^2 <= 1/100.

## Admissible permutations / Lemma 5.5

- [ ] Prove disjoint_swaps_commute.
- [ ] Prove disjoint_swaps_order_independent.
- [ ] Prove disjoint_swaps_reconstruct.
- [ ] Prove disjoint_swaps_fix_outside_support.
- [ ] Prove trim_irrelevant_disjoint_swaps.
- [ ] Prove the possible first-endpoint characterization.
- [ ] Prove the 7D^2 support bound.
- [ ] Prove the interesting-permutation count <= D^(14D^2).
- [ ] Remove or replace partial_matching_count_le if it is only placeholder
      arithmetic rather than a genuine count.
- [ ] Prove tailSizes_valid.
- [ ] Replace fixed_tail_tuple_conditional_chainBound.
- [ ] Prove reindexing into Lemma 4.3 internally.
- [ ] Reproduce s=|S|-5D-1 and the final 1/|S|^2 estimate.

## Lemma 5.6

- [ ] Prove the explicit reversal permutation.
- [ ] Prove reversal preserves the uniform law.
- [ ] Prove reverse-conjugation preserves admissibility.
- [ ] Prove reversal transports FixedOutside.
- [ ] Derive Lemma 5.6 from Lemma 5.5 with no Section-5-specific reversal axiom.

## Lemma 5.3

- [ ] Prove admissible_local_image_subset.
- [ ] Prove local subset-sum injectivity from failure of B0.
- [ ] Prove blocked zero intervals extend left of b or right of b+5D.
- [ ] Prove the 2D-to-D right/left witness dichotomy.
- [ ] Prove distinctness of the t_i in E1.
- [ ] Prove distinctness of the s_i in E2.
- [ ] Replace rightRepairParameters_card_le and leftRepairParameters_card_le.
- [ ] Apply Lemma 5.5/5.6 and derive each 1/100 side bound.

## Greedy repair / Theorem 1.2

- [x] Repair.lean now contains an explicit descending-state induction rather
      than the earlier one-line greedy-repair axiom.
- [ ] Prove remaining swap-support facts used by the repair.
- [ ] Prove exists_after_three_forbidden rather than axiomatizing it.
- [ ] Prove exists_avoiding_three_events from the union bound.
- [ ] Recheck the descending invariant against the prose proof.
- [ ] Verify final indexed/list translation and the alpha<1/2 WLOG reduction.

# G. External-result whitelist

The following may remain axiomatic if documented as genuinely external/general.

- [ ] Cauchy--Schwarz.
- [ ] A general Taylor theorem with Lagrange remainder.
- [ ] Cauchy--Davenport.
- [ ] Standard Fourier character orthogonality on Z_p.
- [ ] Markov inequality / ordinary union bound, if not proved directly.
- [ ] The cited hypergeometric Chernoff estimate
      (Janson--Luczak--Rucinski, Theorem 2.10 and Eq. (2.6)).
- [ ] Routine real-analysis facts not specific to this paper, preferably
      imported from mathlib rather than axiomatized.
- [ ] No whitelisted axiom should mention paper-specific objects such as psi,
      Bset, Dset, chainUpperBound, BadEvent0/1/2/3, Lemma55Event, RepairState,
      or paper-specific constants like 40D except as a proved numerical corollary.

# H. Final audit gates

- [ ] No sorry.
- [ ] No false axiom.
- [ ] No paper-specific axiom hiding a proof from the paper.
- [ ] Every paper-numbered result depends only on earlier paper results and
      whitelisted external inputs.
- [ ] Equations (3.1)--(3.4), (4.1), and (5.1) are derived internally.
- [ ] Every conditional-uniformity claim in Sections 3--5 has an explicit
      finite counting proof.
- [ ] Every numerical constant is reproduced exactly.
- [ ] SOURCE_MAP.md is updated after proof-boundary cleanup.
- [ ] The old completion checklist is not used to claim mathematical proof
      completeness until every item here is checked.
- [ ] Because compilation is disabled by request, the PR continues to state
      that syntax/type correctness remains unverified.
