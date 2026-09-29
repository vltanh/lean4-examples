# Gradient-flow paper formalization — live checklist

Target: Nguyen–Montúfar, *On Parameter Symmetries and Conservation Laws in Gradient Flow* (arXiv:2609.34549v1).

## Branch invariants

- [x] Work on `formalize-gradient-flow-paper`.
- [x] Draft PR opened: #1.
- [x] No `sorry`.
- [x] No `admit`.
- [x] No custom `axiom` declarations.
- [x] Repository pin corrected to Lean 4.26 / mathlib 4.26 in the source commentary.
- [ ] All provisional theorem/interface names eliminated.
- [ ] Source elaborated against the repository pin.
- [ ] Draft PR converted to ready only after the previous two items.

## Paper sections

- [x] Section 2 core definitions and Proposition 2 proof bodies.
- [x] Proposition 1 global-gradient-flow proof body.
- [x] Proposition 4 statement and proof body.
- [x] Proposition 5 / Corollaries 6–7 statement and proof body.
- [x] Propositions 8–9 / Corollary 10 statement and proof body.
- [x] Lie completion definitions and first-integral induction.
- [x] Theorem 12 assembly and gap arithmetic.
- [x] Proposition 14.
- [x] Proposition 15.
- [x] Proposition 16 reflection/slicing argument inlined.
- [x] Theorem 17.
- [x] Matrix-factorization algebra and conserved Gram laws.
- [x] GQA gauge-sharing argument inlined.
- [x] PNN generic locus made explicit and proved open/dense.
- [x] Deep-linear gauge and product-fibre argument inlined.
- [x] Appendix H scalar and 2×2 proof bodies.

## Provisional interfaces still to eliminate

### Differential geometry / ODE
- [ ] `LocalSubmersion.factorization_iff_gradient_mem_span`
- [ ] `ODE.exists_unique_maximal_smooth_localFlow`
- [ ] `LieGroup.connected_invariant_iff_infinitesimal`
- [ ] `Poincare.radialPotential_contDiffOn`
- [ ] `Poincare.gradient_radialPotential_eq`
- [ ] `LieClosure.involutive_of_hasLocalSmoothFrame`
- [ ] `Frobenius.exists_local_firstIntegrals`
- [ ] `SmoothDistribution.exists_orthogonal_localFrame`

### Matrix factorization / attention
- [ ] `Matrix.fullColumnRank_factorization_unique`
- [ ] `MatrixFactorization.complete_balance_laws` — paper cites Marcotte et al. (2023)
- [ ] `MatrixFactorization.symmetryDistribution_eq_kernel_of_squaredLoss`
- [ ] `MatrixFactorization.fderiv_observation_surjective_of_fullColumnRank`
- [ ] `TranEtAl2025.attention_head_identifiability` — paper's Theorem 27
- [ ] `AttentionIdentifiability.exists_local_product_chart`
- [ ] `AttentionIdentifiability.complete_laws_from_factor_blocks`

### Polynomial network
- [ ] `PolynomialIdentifiability.local_scaling_orbit_chart`
- [ ] `PolynomialNetwork.singleGauge_gradient_localFlow`
- [ ] `PolynomialIdentifiability.conserved_gradient_spanned_by_scalings`

### Appendix H spectral algebra
- [ ] `Matrix.posDef_sq_add_pos_scalar_one`
- [ ] `Matrix.posDef_half_add_sqrt_sq_add`
- [ ] `Matrix.sqrt_quadratic_gram_identity`
- [ ] `Matrix.posDef_transpose_mul_self_of_isUnit`
- [ ] `Matrix.unique_posDef_solution_sub_sq_smul_inv`

## Current work queue

1. Inline the easy linear-algebra helper `Matrix.fullColumnRank_factorization_unique`.
2. Inline the one-neuron PNN flow.
3. Replace matrix-factorization kernel/surjectivity helpers with direct differential calculations.
4. Update this checklist after each proof batch.
