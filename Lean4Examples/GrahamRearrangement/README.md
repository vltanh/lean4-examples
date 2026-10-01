# Graham rearrangement formalization

Formalization of Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture* (arXiv:2602.15797v1).

## Status

The source-level mathematical formalization and deep paper-fidelity audit are complete under the requested no-compile policy.

- No `sorry` or `admit` remains.
- Every numbered Fact, Lemma, Corollary, and Theorem in the paper has an internal theorem body.
- Every finite sampling, conditioning, permutation-invariance, counting, and repair argument proved in the paper is internal.
- The project contains **no custom axioms**. The hypergeometric estimate cited by the paper as [8, Theorem 2.10 and Eq. (2.6)] is formalized in `External/Hypergeometric/` from a finite without-replacement sampling model and mathlib's proved Hoeffding lemma.
- Reference [8] remains recorded as provenance: S. Janson, T. Łuczak, and A. Ruciński, *Random Graphs*, John Wiley & Sons, 2011.
- No CI workflow is present.
- Lean has not been compiled or typechecked, by explicit request.

## Layout

```text
Lean4Examples/
├── GrahamRearrangement.lean
└── GrahamRearrangement/
    ├── Introduction.lean
    ├── External.lean
    ├── External/
    │   ├── Hypergeometric.lean
    │   └── Hypergeometric/
    │       ├── Sampling.lean
    │       ├── Hoeffding.lean
    │       └── Tails.lean
    ├── Probability.lean
    ├── Preliminaries.lean
    ├── BooleanSlice.lean
    ├── BooleanSlice/
    │   ├── Definitions.lean
    │   ├── External.lean
    │   ├── Fourier.lean
    │   ├── Lemmas.lean
    │   └── Theorem.lean
    ├── Combinatorial.lean
    ├── Combinatorial/
    │   ├── Definitions.lean
    │   ├── External.lean
    │   ├── Lemma41.lean
    │   ├── Corollary14.lean
    │   ├── Corollary42.lean
    │   └── Lemma43.lean
    ├── Rearrangement.lean
    ├── Rearrangement/
    │   ├── Definitions.lean
    │   ├── External.lean
    │   ├── IntervalLemmas.lean
    │   ├── Parameters.lean
    │   ├── Lemma51.lean
    │   ├── Lemma54.lean
    │   ├── Lemma52.lean
    │   ├── Lemma55.lean
    │   ├── Reversal.lean
    │   ├── Lemma56.lean
    │   ├── Lemma53.lean
    │   ├── Repair.lean
    │   └── BadEvents.lean
    ├── Main.lean
    ├── SOURCE_MAP.md
    ├── CHECKLIST.md
    ├── DEEP_AUDIT_CHECKLIST.md
    └── README.md
```

## Fidelity notes

Two paper-text inconsistencies are recorded explicitly.

1. Two Section 3 transition sentences use (B_{32t}), whereas Lemmas 3.2/3.3 and the later proof use (B_{2000t}). The formalization follows the numbered lemmas and proof.
2. Lemma 3.2 prints (265t/m) for the contribution inside (J_{\chi,t}), but the next line uses (4\cdot256=1024) and then (2000-1024=976). The radius (16\sqrt{t/m}) gives (256t/m), so the formalization follows the intended (256\to1024\to976) calculation and documents the printed (265) as an arithmetic typo.

`External/Hypergeometric/Sampling.lean` proves the finite without-replacement sampling law; `Hoeffding.lean` proves the exponential-moment bound; and `Tails.lean` derives the exact two tail estimates used in Section 3.

See `DEEP_AUDIT_CHECKLIST.md` for the completed axiom-free proof-boundary audit and `SOURCE_MAP.md` for the paper-to-Lean map.

## Verification boundary

Because compilation was explicitly forbidden, completion means the source proof architecture, axiom boundary, and paper-fidelity audit are complete. It is not a claim that Lean has accepted the files; syntax/elaboration/type correctness remain unverified until compilation is later authorized.
