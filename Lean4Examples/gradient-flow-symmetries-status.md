# Gradient-flow paper formalization — live checklist

Target: Nguyen–Montúfar, *On Parameter Symmetries and Conservation Laws in Gradient Flow* (arXiv:2609.34549v1).

This checklist tracks the **source-level proof pass**. Per project instruction, Lean compilation and GitHub CI are not completion criteria for this pass and are not being run.

## Global invariants

- [x] Work on `formalize-gradient-flow-paper`.
- [x] Draft PR opened: #1.
- [x] Source split into stable paper/support modules.
- [x] Zero `sorry` in all eight paper modules.
- [x] Zero `admit` in all eight paper modules.
- [x] Zero custom `axiom` declarations in all eight paper modules.
- [x] Zero custom external-result typeclasses remain.
- [x] All CI workflow/configuration removed from the PR branch.
- [x] Compilation/CI explicitly excluded from the current proof-completion pass.
- [x] Machine-readable theorem/dependency manifest present at
  `Lean4Examples/GradientFlowPaper/dependency-manifest.json`.

# Stage 1 — Paper-facing formalization

## Statement and proof coverage

- [x] Section 2 core definitions.
- [x] Proposition 1.
- [x] Proposition 2.
- [x] Definition 3 / functional independence.
- [x] Proposition 4.
- [x] Proposition 5 / Corollaries 6–7.
- [x] Propositions 8–9 / Corollary 10.
- [x] Definition 11 / completeness notions.
- [x] Theorem 12 and gap arithmetic.
- [x] Proposition 14.
- [x] Proposition 15.
- [x] Proposition 16.
- [x] Theorem 17.
- [x] Proposition 18 (GQA/MHSA).
- [x] Proposition 19 (PNNs).
- [x] Proposition 20 (deep square linear networks).
- [x] Theorems 21–22.
- [x] Propositions 23–25.
- [x] Lemma 26.
- [x] Theorem 27.
- [x] Lemma 28.
- [x] Lemma 29.
- [x] Appendix B.2 scalar example.

## Paper-internal obligations

- [x] Local factorization for Proposition 4.
- [x] Connected Lie-group infinitesimal invariance/generation.
- [x] Poincaré/local potential construction.
- [x] Maximal smooth local-flow existence and uniqueness.
- [x] Lie-completion construction and involutivity.
- [x] Smooth orthogonal-complement local frames.
- [x] GQA head matching from Theorem 27.
- [x] GQA factor-block completeness from Lemma 28 + Theorem 17.
- [x] PNN scaling generators and conservation laws.
- [x] PNN tangent-to-scaling-orbit theorem.
- [x] PNN fixed-fibre local orbit isolation from finite identifiability.
- [x] PNN extension from the a.e. finite-fibre locus to the full regular neighborhood by continuity.
- [x] Deep-linear product-fibre argument.
- [x] Appendix H spectral closure.

# Stage 2 — Dependency closure completed in this source pass

## Standard geometry / ODE

- [x] Local submersion/factorization discharged from Mathlib's finite-dimensional implicit-function theorem.
- [x] Maximal smooth local flows discharged using the vendored minimal TauCeti ODE chain plus internal gluing/maximality.
- [x] Connected Lie-group generation discharged internally.
- [x] Star-shaped/local Poincaré lemma discharged internally.
- [x] Frobenius hard direction proved internally by rank induction:
  - [x] one-field flow box;
  - [x] smooth local-chart transport and Lie-bracket naturality;
  - [x] time-dependent ODE uniqueness;
  - [x] transverse-span invariance;
  - [x] rank-zero case;
  - [x] successor-rank reduction;
  - [x] local submersion-to-first-integral conversion.
- [x] Smooth orthogonal local frames proved by local basis extension + pointwise Gram–Schmidt.
- [x] Lie-completion involutivity proved from local Lie-word frames.

## Literature inputs used by Nguyen–Montúfar

- [x] **Tran et al. attention identifiability / Theorem 27** proved directly in
  `Attention.lean`:
  - [x] simultaneous separation of finitely many bilinear forms;
  - [x] reciprocal-weight independence;
  - [x] special repeated-token input calculation;
  - [x] open-set rigidity;
  - [x] final head-identifiability theorem.
- [x] **Marcotte et al. matrix-factorization completeness / Lemma 28** proved directly in
  `MatrixFactorization.lean`:
  - [x] full-rank fibre and tangent gauge form;
  - [x] normal fields and first Lie brackets;
  - [x] skew-gauge detection;
  - [x] symmetric matrix basis;
  - [x] completeness of Gram-difference laws.
- [x] **Usevich et al. generic finite identifiability** is represented source-faithfully as the explicit Proposition 19 hypothesis
  `GenericallyFiniteToOne A := ∀ᵐ p, FiniteToOneAt A p`.
  - [x] finite-to-one means finitely many classes modulo diagonal scalings, with finite permutations absorbed into the representative set;
  - [x] no stronger open finite-to-one neighborhood is assumed;
  - [x] finite-fibre local scaling-orbit isolation is proved internally;
  - [x] the a.e. generic result is extended to the whole open nonzero-bias locus by continuity.
  - [ ] A standalone formalization of Usevich et al.'s architecture-specific sufficient conditions for `GenericallyFiniteToOne` is **not part of Nguyen–Montúfar's source-level proof** and remains separate literature work if desired.

## Appendix H

- [x] Positive square roots identified with Mathlib CFC square roots.
- [x] Commutation with the symmetric base matrix.
- [x] Gram candidate positive definite.
- [x] Quadratic Gram identity.
- [x] Positive-definite solution uniqueness.
- [x] Lemma 29 no longer depends on spectral helper interfaces.

# PNN audit repair

The split audit found a real defect in the earlier monolithic draft:

- [x] The local functional-fibre/scaling-orbit conclusion had been moved behind
  `HasPNNGenericRegime.local_regime` and incorrectly counted as a completed proof.
- [x] That typeclass was removed.
- [x] Canonical bias-ratio coordinates were restored.
- [x] Canonical bias-normalization slice was formalized.
- [x] A finite fibre modulo scaling was proved to have an isolated scaling orbit at every nonzero-bias point.
- [x] The scaling-orbit tangent theorem was proved directly.
- [x] The over-strong `GenericFiniteToOneAt` open-neighborhood adapter was removed.
- [x] Proposition 19 now uses the cited source's measure-generic finite-to-one hypothesis literally.

# Packaging

- [x] `Core.lean`
- [x] `Geometry.lean`
- [x] `Inheritance.lean`
- [x] `MatrixFactorization.lean`
- [x] `Attention.lean`
- [x] `Polynomial.lean`
- [x] `DeepLinear.lean`
- [x] `Examples.lean`
- [x] Aggregate module `Lean4Examples.GradientFlowPaper`.
- [x] Compatibility import `gradient-flow-symmetries.lean`.
- [x] Library root `Lean4Examples.lean`.
- [x] Machine-readable dependency/theorem manifest.

# Current source-level checkpoint

- [x] Every selected Nguyen–Montúfar numbered statement has a Lean declaration.
- [x] Every paper-internal argument currently in scope has source-level Lean proof code.
- [x] No paper-internal conclusion is hidden behind a custom dependency typeclass.
- [x] No custom external-result typeclass remains.
- [x] Zero `sorry`.
- [x] Zero `admit`.
- [x] Zero custom `axiom`.
- [x] Proposition 19's remaining literature premise is an explicit theorem hypothesis, not an assumed implementation interface.
- [x] Source-level proof pass complete.

## Explicitly deferred by instruction

- [ ] Lean elaboration/compilation against the repository pin.
- [ ] `#print axioms` / kernel audit requiring elaboration.
- [ ] Any GitHub CI workflow.
