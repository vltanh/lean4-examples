# Deep proof audit checklist — complete

Paper: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture*,
arXiv:2602.15797v1.

This is the authoritative proof-boundary checklist.

## Audit rule

Only a result which the paper itself imports from another source may remain an
axiom. Results described as easy, standard, routine, probabilistic bookkeeping,
finite counting, Fourier algebra, conditioning, or permutation invariance are
proved internally.

## A. Statement fidelity

- [x] Target pinned to arXiv:2602.15797v1.
- [x] Theorem 1.2 has exactly 0<alpha<1, C_alpha>0, prime p,
      S subset Z_p minus {0}, and C_alpha <= |S| <= p^(1-alpha).
- [x] Theorem 1.3 uses one absolute constant and the exact
      C log|S| <= m <= 10^-3 |S|/log|S| range.
- [x] Corollary 1.4 uses the exact 0<epsilon<1 and
      m <= (1-epsilon)|S| hypotheses.
- [x] All Section 5 intervals are translated explicitly between paper positions
      1,...,n and Fin n.
- [x] The partial-sum formulation is proved equivalent to the nonzero-segment
      formulation used in Section 5.
- [x] Composition order for position permutations agrees with the paper.
- [x] Admissible collections, blocked choices, B0,B1,B2,B3, and E1,E2 match
      the paper's definitions.
- [x] The constants 1/100, 3/100, 1/25, 5D, 10D, 20D, 30D, 40D and all
      C_alpha lower bounds are retained.

## B. Paper-text fidelity notes

- [x] The two Section 3 transition sentences using B_32t are documented as
      inconsistent with Lemmas 3.2/3.3 and the final proof, which use B_2000t.
      The formalization follows the numbered lemmas/proof.
- [x] The center y_chi is chosen once, independently of t, from the smallest
      positive scale with chi in D_t, as stated in the paper.
- [x] J_{chi,t} is a subset of all Z_p, not only of S.
- [x] The balanced-partition model uses the intended quotient/remainder block
      sizes.
- [x] Lemma 3.2's PDF line printing 265t/m is documented as an arithmetic typo:
      the definition of J_{chi,t} gives the intended 256t/m, which is exactly
      what is needed for the next displayed 4*256=1024 and 2000-1024=976
      calculation. Lean formalizes this intended 256 -> 1024 -> 976 argument.

## C. Section 2

- [x] Fact 2.1 is proved by nearest integers, the triangle inequality, and
      Cauchy--Schwarz.
- [x] Fact 2.2 is proved by periodicity/symmetry and the same Taylor/Lagrange
      remainder expansions used in the paper.
- [x] Fact 2.3 is proved from integer representatives and Fact 2.1.
- [x] Fact 2.4 is proved by repeated Cauchy--Davenport.
- [x] Fact 2.5 is reduced to Fact 2.2 through the explicit character real-part
      identity.
- [x] No Section 2 argument is axiomatized.

## D. Section 3

- [x] The balanced-partition sample space is explicit and nonempty.
- [x] The one-choice-per-block experiment is proved uniform on size-m subsets.
- [x] Conditional block remainders are proved uniform by finite permutation
      symmetry.
- [x] Equation (3.1) is derived from character orthogonality and finite product
      factorization.
- [x] Equation (3.2) is derived from Fact 2.5.
- [x] Equations (3.3) and (3.4) are proved internally.
- [x] Lemmas 3.1--3.7 are proved internally.
- [x] The character-square calculation in Lemma 3.6 is derived from
      orthogonality.
- [x] The final dyadic split in Theorem 1.3 is proved internally.
- [x] The only axiomatized Section 3 input is the hypergeometric Chernoff
      estimate explicitly cited by the paper from [8].

## E. Strict external axiom boundary

- [x] hypergeom_quarter_lower_tail is the specialization used in Lemma 3.1 of
      the hypergeometric Chernoff bound cited as [8, Theorem 2.10 and Eq. (2.6)].
- [x] hypergeom_three_quarters_lower_tail is the specialization used in Lemma
      3.3 of the same cited result.
- [x] Reference [8] is S. Janson, T. Łuczak, and A. Ruciński, *Random Graphs*,
      John Wiley & Sons, 2011.
- [x] No Cauchy--Schwarz, Taylor, Cauchy--Davenport, Fourier-orthogonality,
      Markov, union-bound, asymptotic, or finite-probability statement is an
      axiom in this project; those are theorem bodies or library theorems.
- [x] No paper-specific object appears in an axiom statement other than the two
      direct hypergeometric specializations.

## F. Section 4

- [x] Lemma 4.1's two-stage subset law is proved by finite counting.
- [x] Corollary 1.4's split sampling law is proved internally.
- [x] Corollary 4.2 uses full exposed histories and conditional uniformity, not
      an invalid product-of-marginals shortcut.
- [x] The formerly false finiteConditionalProductBound declaration is gone.
- [x] Equation (4.1) is proved by the paper's induction.
- [x] The omitted-gap factorization/reversal in Lemma 4.3 is internal.
- [x] Combinatorial/External.lean contains no axioms.

## G. Section 5 random orderings and conditioning

- [x] Nonemptiness of indexed orderings is proved.
- [x] Fixed position sets have uniform image subsets.
- [x] Conditioning on exposed positions leaves a uniform bijection on the
      remaining positions/values.
- [x] Fixed nested unexposed index sets have exactly the chainMass law.
- [x] Position-permutation invariance and conditional invariance are proved.
- [x] Fiber averaging and joint-event multiplication are proved from finite
      cardinality ratios.

## H. Lemmas 5.1--5.4

- [x] Lemma 5.1's endpoint reindexing and reciprocal-square-root sum are
      internal.
- [x] Equation (5.1)'s distinct-subset collision estimate is proved by exposing
      all but one coordinate in the symmetric difference.
- [x] The B0 parameter count counts only the actual 20D-window parameters.
- [x] Lemma 5.4 is proved with the exact 1/100 bound.
- [x] Lemma 5.2 uses the paper's minimal-b0, distinct-left-endpoint,
      conditional-prefix-chain, Corollary 4.2, and Lemma 4.3 argument.

## I. Lemmas 5.5--5.6

- [x] Disjoint swaps commute and their product is independent of enumeration.
- [x] An admissible collection is reconstructible from its product permutation.
- [x] Irrelevant swaps are trimmed internally.
- [x] The 7D^2 support count and D^(14D^2) interesting-permutation count are
      internal.
- [x] After exposing [b,b'], each interval is split into its exposed head and
      nested unexposed tail exactly as in the paper.
- [x] The fixed-tail conditional law is reduced to the proved nested-chain law.
- [x] Lemma 5.6 is obtained by explicit order reversal; reversal preserves the
      required admissibility/fixed-window properties.

## J. Lemma 5.3 and final repair

- [x] Failure of B0 gives the local subset-sum injectivity used in the
      blocked-choice split.
- [x] The 2D -> D right/left dichotomy is internal.
- [x] The parameter counts for E1,E2 are internal.
- [x] Lemmas 5.5 and 5.6 yield the two 1/100 side bounds.
- [x] Lemma 5.3 yields 1/25.
- [x] The descending greedy repair is an explicit finite induction.
- [x] The final union-bound existence argument is internal.
- [x] Theorem 1.2 is assembled from the same bad-event/repair architecture as
      the paper.

## K. Final source gates

- [x] No sorry.
- [x] No admit.
- [x] No false axiom.
- [x] No paper-internal proof is hidden behind an axiom.
- [x] The only axioms are the two [8]-cited hypergeometric estimates.
- [x] Every numbered Fact, Lemma, Corollary, and Theorem has an internal theorem
      body.
- [x] Equations (3.1)--(3.4), (4.1), and (5.1) are derived internally.
- [x] Every conditional-uniformity step used in Sections 3--5 is represented by
      an explicit finite counting/symmetry theorem.
- [x] No CI workflow is present.
- [x] No compilation/typechecking has been performed, per explicit request.

## Verification boundary

This checklist certifies the source-level mathematical proof boundary and
paper-fidelity audit. Because compilation was explicitly forbidden, it does not
claim that Lean has accepted the source. Syntax, elaboration, theorem names, and
type correctness remain unverified until compilation is later authorized.
