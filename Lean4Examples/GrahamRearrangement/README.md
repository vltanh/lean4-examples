# Graham rearrangement formalization

Formalization of Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture* (arXiv:2602.15797).

## Layout

```text
Lean4Examples/
├── GrahamRearrangement.lean
└── GrahamRearrangement/
    ├── Introduction.lean
    ├── Preliminaries.lean
    ├── BooleanSlice.lean
    ├── Combinatorial.lean
    ├── Rearrangement/
    │   ├── Definitions.lean
    │   └── BadEvents.lean
    ├── Main.lean
    ├── CHECKLIST.md
    └── README.md
```

The dependency flow follows the paper:

```text
Introduction
    ↓
Preliminaries          (Section 2)
    ↓
BooleanSlice           (Section 3)
    ↓
Combinatorial          (Section 4)
    ↓
Rearrangement/Definitions
    ↓
Rearrangement/BadEvents
    ↓
Main                   (Theorem 1.2)
```

`Lean4Examples.GrahamRearrangement` is the umbrella module.

## Formalization policy

`CHECKLIST.md` is the source of truth for completeness. A numbered paper result is only complete when its paper-faithful statement and proof are present without `sorry`, custom axioms, or unproved replacement hypotheses.

The reorganization itself does not claim additional proof completion. Existing declarations and proof placeholders were moved into paper-oriented modules without intentionally changing their mathematical content.

Per request, no CI workflow is included and this reorganization is not compiled as part of the task.
