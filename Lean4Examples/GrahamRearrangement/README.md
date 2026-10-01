# Graham rearrangement formalization

Formalization of Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture* (arXiv:2602.15797v1).

## Layout

```text
Lean4Examples/
├── GrahamRearrangement.lean
└── GrahamRearrangement/
    ├── Introduction.lean
    ├── External.lean
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
    │   ├── ReversalExternal.lean
    │   ├── Lemma56.lean
    │   ├── Lemma53.lean
    │   ├── Repair.lean
    │   └── BadEvents.lean
    ├── Main.lean
    ├── SOURCE_MAP.md
    ├── CHECKLIST.md
    └── README.md
```

## Dependency flow

```text
Introduction
    ↓
Preliminaries                        Section 2
    ↓
BooleanSlice/{Definitions,Fourier,Lemmas,Theorem}
                                     Section 3
    ↓
Combinatorial/{Lemma41,Corollary14,Corollary42,Lemma43}
                                     Section 4
    ↓
Rearrangement/{Definitions,IntervalLemmas,Parameters}
    ↓
Lemma51 → Lemma54 → Lemma52
    ↓
Lemma55 → Lemma56 → Lemma53
    ↓
Repair → BadEvents
    ↓
Main                                 Theorem 1.2
```

`Lean4Examples.GrahamRearrangement` is the umbrella module.

## Formalization policy

The paper-facing source has been filled in, but a subsequent deep audit found paper-internal proof steps still hidden behind External axioms. Mathematical audit completeness is therefore **not yet claimed**:

- every numbered Fact, Lemma, Corollary, and Theorem has a theorem declaration, but some theorem bodies still depend on External axioms that must be internalized;
- the Lean source tree contains no `sorry`;
- external/general mathematical, probabilistic, sampling, and permutation inputs are axiomatized only in files whose names contain `External`, per request;
- the exact constants and bad-event architecture of the paper are retained;
- `SOURCE_MAP.md` records the paper-to-Lean mapping and fidelity notes.

`DEEP_AUDIT_CHECKLIST.md` is the authoritative missing-proof checklist. `CHECKLIST.md` records the earlier source-coverage pass.

## Verification status

No CI workflow is included and no Lean compilation/typechecking was performed, by explicit request. Completion here means the source formalization and dependency structure are filled in; it is **not** a claim that Lean has accepted the files.
