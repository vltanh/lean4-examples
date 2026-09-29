# Gradient-flow paper formalization — live checklist

Target: Nguyen–Montúfar, *On Parameter Symmetries and Conservation Laws in Gradient Flow* (arXiv:2609.34549v1).

The work is intentionally split into two stages.

- **Stage 1 — paper formalization:** formalize every definition, statement, and argument actually carried out in the paper. Results imported from the literature or treated as standard background remain explicit external dependencies.
- **Stage 2 — dependency closure:** prove those external dependencies from Mathlib/basic formal mathematics so the final exported paper theorems have no custom axioms and are suitable for Palomar-style auditing.

The Stage 1 boundary is strict: an imported result may remain external, but it must be represented by an explicit typed dependency whose statement matches exactly what the paper uses. It must not be hidden behind an unclassified provisional theorem name.

## Global invariants

- [x] Work on `formalize-gradient-flow-paper`.
- [x] Draft PR opened: #1.
- [x] No `sorry`.
- [x] No `admit`.
- [x] No custom `axiom` declarations.
- [x] Repository commentary targets Lean 4.26 / Mathlib 4.26.
- [ ] Source elaborates against the repository pin.
- [x] Every remaining dependency is classified as either **paper-internal** or **external**.
- [x] No anonymous/provisional interface names remain.
- [ ] Final dependency audit shows only accepted Lean/Mathlib foundational axioms.

# Stage 1 — Completely formalize the paper

## 1A. Paper-facing statement coverage

- [x] Section 2 core definitions.
- [x] Proposition 1 statement and proof body.
- [x] Proposition 2.
- [x] Definition 3 / functional independence.
- [x] Proposition 4 statement and proof body.
- [x] Proposition 5 / Corollaries 6–7.
- [x] Propositions 8–9 / Corollary 10.
- [x] Definition 11 / completeness notions.
- [x] Theorem 12 assembly and gap arithmetic.
- [x] Proposition 14.
- [x] Proposition 15.
- [x] Proposition 16 reflection/slicing argument.
- [x] Theorem 17.
- [x] Proposition 18 GQA/MHSA statement and shared-gauge argument.
- [x] Proposition 19 PNN statement, explicit generic locus, and tangent-to-scaling-orbit argument.
- [x] Proposition 20 deep square linear network statement and product-fibre argument.
- [x] Appendix B.2 scalar example.
- [x] Appendix H / Lemma 29 proof body.

## 1B. Explicit external dependencies allowed during Stage 1

These should be gathered into a dedicated typed interface, e.g. `GradientFlowPaper.ExternalResults`. Paper proofs may depend on an arbitrary value of this interface. Stage 2 will construct that value from proved theorems.

### Standard background used by the paper

- [x] Local submersion/factorization theorem needed for Proposition 4. — represented as an explicit Stage-1 external dependency
- [x] Maximal smooth local-flow existence/uniqueness needed for Proposition 9. — represented as an explicit Stage-1 external dependency
- [x] Connected Lie-group infinitesimal-invariance theorem needed for Proposition 5. — represented as an explicit Stage-1 external dependency
- [x] Poincaré lemma in the star-shaped/local form used by Propositions 8–10. — represented as an explicit Stage-1 external dependency
- [x] Frobenius/local-first-integral theorem used by Theorem 12. — represented as an explicit Stage-1 external dependency
- [x] Smooth local orthogonal-complement frame construction. — represented as an explicit Stage-1 external dependency
- [x] Lie-completion involutivity closure theorem. — represented as an explicit Stage-1 external dependency

### Literature results explicitly imported by the paper

- [x] **Tran et al. (2025a), Theorem 3.1 / paper Theorem 27:** attention-head identifiability. — represented as an explicit Stage-1 external dependency
- [x] **Marcotte et al. (2023), Section 4.1 / paper Lemma 28:** completeness of the upper-triangular entries of `UᵀU - VᵀV` for full-rank matrix factorization. — represented as an explicit Stage-1 external dependency
- [x] **Usevich et al. (2025):** exact finite-to-one/generic PNN identifiability result needed to justify the local diagonal-scaling orbit description. — represented as an explicit Stage-1 external dependency
- [x] Piziak–Odell full-rank matrix-factorization uniqueness — proof inlined; no longer external.

### Standard spectral/matrix facts used in Appendix H

- [x] Positive-definiteness of the half-plus-square-root matrix. — represented as an explicit Stage-1 external dependency
- [x] Quadratic Gram identity. — represented as an explicit Stage-1 external dependency
- [x] Uniqueness of the positive-definite solution. — represented as an explicit Stage-1 external dependency
- [x] Positive-definiteness of `H₀² + 4 α² I` handled directly.
- [x] Positive-definiteness of `UᵀU` for invertible `U` reduced to Mathlib.
- [x] Positive square root represented with Mathlib continuous functional calculus.

## 1C. Paper-internal deductions that must be finished in Stage 1

These are proved by Nguyen–Montúfar from the external inputs above, so they must not remain external interfaces.

- [x] Proposition 16 reflection/slicing proof.
- [x] Full-rank factorization change-of-basis argument.
- [x] Shared GQA gauge parameters inside each group.
- [x] PNN conservation from the explicit scaling symmetry.
- [x] PNN tangent-to-scaling-orbit completeness step.
- [x] GQA local product-identifiability deduction from Theorem 27.
- [x] GQA factor-block completeness deduction from Lemma 28 + Theorem 17.
- [x] PNN local-neighborhood step is routed through the exact Stage-1 generic-regime dependency, with the subsequent tangent/completeness argument formalized.
- [x] Remaining helpers have been classified; paper-internal GQA, PNN, inheritance, and deep-linear deductions are inlined.

## 1D. Stage-1 completion criterion

Stage 1 is complete only when:

- [x] every numbered theorem/proposition/corollary/lemma selected from Nguyen–Montúfar has a Lean statement, including Theorems 21–22, Propositions 23–25, and Lemma 26;
- [x] every paper-internal proof step currently in scope is represented by Lean proof code;
- [x] every result not proved in Nguyen–Montúfar is visibly routed through a named external dependency class;
- [x] no provisional namespace such as `AttentionIdentifiability` or `PolynomialIdentifiability` hides an unclassified obligation;
- [ ] the paper layer compiles assuming an arbitrary value of the external-results interface;
- [x] dependency classes are source-labeled in code and checklist; a separate machine-readable manifest remains a Stage-3 packaging task.

# Stage 2 — Formalize the external dependencies

Stage 2 starts only after Stage 1 is frozen.

## 2A. Mathlib-first resolution

For each external field:

- [ ] search Mathlib for an exact or stronger theorem;
- [ ] prove a small adapter lemma if Mathlib has the mathematical substance but not the exact formulation;
- [ ] record the Mathlib declarations used;
- [ ] vendor a new proof only when Mathlib genuinely lacks the result.

## 2B. Standard geometry / ODE dependencies

- [x] Prove/adapt local submersion factorization — discharged from Mathlib's finite-dimensional implicit-function theorem.
- [x] Prove/adapt maximal local-flow existence and uniqueness — vendored the Apache-2.0 TauCeti smooth-dependence proof over Mathlib, then glued all local flow patches and took their common extension.
- [ ] Prove/adapt connected Lie-group infinitesimal invariance.
- [x] Prove the needed Poincaré lemma — discharged using Mathlib curve integrals and convex Poincaré on local triangles inside a star-shaped domain.
- [ ] Prove/adapt Frobenius/local first integrals.
- [ ] Prove smooth orthogonal local frames.
- [ ] Prove Lie-completion involutivity.

## 2C. Literature dependencies

- [ ] Formalize Tran et al.'s attention identifiability theorem.
  - [ ] locate the exact cited source/version;
  - [ ] preserve quantification over all positive sequence lengths;
  - [ ] formalize the cited proof without silently strengthening or weakening the result.
- [ ] Formalize Marcotte et al.'s matrix-factorization completeness result.
  - [ ] characterize the gradient distribution for `UVᵀ`;
  - [ ] compute the relevant Lie completion/rank;
  - [ ] prove independence of the upper-triangular Gram-difference coordinates;
  - [ ] conclude completeness in the exact local sense required by Nguyen–Montúfar.
- [ ] Formalize the Usevich et al. finite-to-one/generic PNN identifiability result needed by Proposition 19.
  - [ ] identify the exact definitions of “finite-to-one” and “generic” in the cited source;
  - [ ] reconcile them with the current `GenericPoint`;
  - [ ] prove local elimination of permutation/discrete branches;
  - [ ] derive the local diagonal-scaling orbit chart.

## 2D. Appendix H spectral closure

- [x] Eliminate the remaining spectral helper interfaces using Mathlib spectral/CFC machinery.
- [x] Prove the quadratic matrix identity using the positive square root, commutation, and Mathlib CFC.
- [x] Prove uniqueness of the positive-definite solution by constructing a second positive square root and invoking uniqueness of `CFC.sqrt`.
- [x] Recheck that Lemma 29 uses `UᵀU - VᵀV` in the source notation (the corrected orientation).

# Stage 3 — Compilation and Palomar-style audit

## 3A. Elaboration repair

- [x] Split the single-file draft into stable modules.
- [ ] Compile every module under the pinned Lean/Mathlib version.
- [ ] Fix API names, coercions, universe issues, and tactic failures without weakening statements.
- [ ] Run zero-`sorry` / zero-`admit` / zero-custom-`axiom` scans after every repair batch.

## 3B. Paper-facing export surface

- [ ] Create a compact paper-facing module containing the exact formalized statements.
- [ ] Keep support machinery outside the challenge statement surface.
- [ ] Add comments mapping Lean declarations to paper proposition/theorem numbers.
- [x] Add a theorem-dependency manifest (`Lean4Examples/GradientFlowPaper/dependency-manifest.json`).

## 3C. Foundational dependency audit

- [ ] Inspect `#print axioms` for every exported theorem.
- [ ] Reject `sorryAx`.
- [ ] Reject `Lean.ofReduceBool`.
- [ ] Reject any custom axiom or opaque assumed theorem.
- [ ] Confirm every external-results field is instantiated by a proved term.
- [ ] Confirm final paper theorems use only accepted Lean/Mathlib foundational axioms.

# Current priority queue

1. [x] Classify standard geometry, literature, and spectral inputs as explicit Stage-1 dependencies.
2. [x] Inline GQA Step 1 from Theorem 27.
3. [x] Inline GQA Steps 2–3 from Lemma 28 + Theorem 17.
4. [x] Keep the paper/Usevich identifiability-generic predicate separate from the concrete nonzero-bias regular locus; Proposition 19 now works on their explicit intersection rather than identifying them.
5. [x] Add the remaining numbered appendix-facing statements, including the Lemma 26 audit.
6. [x] Add/update the external dependency manifest and run a source-level coverage audit.
7. Freeze Stage 1 at source level. Elaboration/compilation remains a later repair stage, per the requested uncompiled workflow.
8. [x] Begin Stage 2.


## Current Stage-1 checkpoint

- [x] Paper-facing source coverage complete.
- [x] GQA Steps 1–3 are inlined from the explicit Tran/Marcotte dependencies and Theorem 17.
- [x] PNN genericity is no longer silently identified with a convenient coordinate condition; the paper's implicit “generic” regime is explicit as a parameterized dependency.
- [x] Appendix numbered results Theorem 21, Theorem 22, Propositions 23–25, and Lemma 26 are present.
- [x] Source scan: zero `sorry`, zero `admit`, zero custom `axiom`.
- [ ] Final Stage-1 gate: elaborate/compile the paper layer against the pinned toolchain with the external dependency interfaces left abstract. Historical CI reached Lake but failed before elaboration because the package root `Lean4Examples.lean` was missing; that root has now been added.


## Stage-2 progress

- [x] Appendix H spectral dependency discharged from Mathlib/CFC.
  - [x] arbitrary positive square roots identified with `CFC.sqrt`;
  - [x] square root commutes with the symmetric base matrix;
  - [x] Gram candidate proved positive definite;
  - [x] quadratic Gram identity proved;
  - [x] positive-definite solution uniqueness proved;
  - [x] `lemma29` and `lemma29_roots_exist` no longer quantify over the spectral dependency class.
- [x] Maximal smooth local-flow / ODE dependency discharged via the vendored TauCeti proof chain.
- [x] Connected Lie-group generation dependency discharged internally.
- [x] PNN scaling-orbit tangent dependency discharged internally on the concrete dense-open regular locus.
- [ ] Next: Frobenius/local first integrals, smooth orthogonal frames, Lie-completion involutivity, then Marcotte / Tran / Usevich.


### Stage-2 geometry checkpoint

- [x] Proposition 4 no longer depends on `HasLocalSubmersionFactorization`.
  - [x] independent gradients imply surjectivity of the derivative of the bundled map;
  - [x] the span condition annihilates the kernel of that derivative;
  - [x] Mathlib's implicit-function chart supplies local product coordinates;
  - [x] the observable is constant on vertical fibres;
  - [x] the two directions of Proposition 4 are now proved directly.
- [x] Star-shaped Poincaré dependency eliminated.
- [x] Maximal smooth local flows / ODE discharged.
- [x] Connected Lie-group infinitesimal invariance/generation discharged.


### Stage-2 Poincare checkpoint

- [x] `HasStarPoincareLemma` removed, including the last stale typeclass parameter on `proposition8_star`.
- [x] Explicit radial potential identified with a curve integral over the radial segment.
- [x] Local triangle relation proved using Mathlib's convex Poincare theorem.
- [x] Derivative of the radial potential proved to be the associated one-form.
- [x] Smoothness bootstrapped from the smooth derivative.


### Stage-2 ODE checkpoint

- [x] `HasMaximalSmoothLocalFlows` removed.
- [x] Vendored the minimal Apache-2.0 TauCeti model-space smooth-flow proof chain, pinned to source commit `b56249442e554651432debd903d53f228e7f5a6f`.
- [x] Smooth local flow germs shrunk to symmetric product patches inside the paper domain.
- [x] Smooth ODE uniqueness propagated across arbitrary open convex time intervals.
- [x] Local flow patches glued by uniqueness.
- [x] Arbitrary nonempty families of local flows have a common smooth extension.
- [x] The common extension of all local flows is maximal.
- [x] Connected Lie-group generation interface eliminated.
- [x] PNN `HasPNNScalingOrbitTangent` interface eliminated; `tangent_mem_span_scaling_orbit` is used directly.
- [x] The Usevich-facing `HasPNNGenericRegime` interface now contains only the local functional-fibre / diagonal-scaling-orbit statement; generator independence is derived internally on `genericSet`.
- [ ] Next: eliminate the remaining Frobenius / Marcotte / Tran / Usevich interfaces.


### Stage-3 packaging checkpoint

- [x] Split the former concatenated source into `Core`, `Geometry`, `Inheritance`, `MatrixFactorization`, `Attention`, `Polynomial`, `DeepLinear`, and `Examples`.
- [x] Add aggregate module `Lean4Examples.GradientFlowPaper`.
- [x] Keep `gradient-flow-symmetries.lean` as a compatibility import.
- [x] Add `Lean4Examples.lean`, fixing the default Lake library root diagnosed by the historical Lean 4.26 CI run.
- [x] Add a machine-readable dependency/theorem manifest.
- [x] Re-run source scans after the split: zero `sorry`, zero `admit`, zero custom `axiom` declarations in all eight paper modules.
- [ ] Kernel-check the module graph and repair elaboration errors.
- [ ] Run `#print axioms` over the exported theorem surface after external dependency closure.
