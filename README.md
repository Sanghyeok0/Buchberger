# Buchberger Algorithm Formalization

This repository is the companion artifact and documentation site for a Lean 4
formalization of relation-theoretic polynomial reduction, the Groebner basis
criterion, and Buchberger's algorithm.

The canonical Lean sources live in the author's
[`mathlib4` fork](https://github.com/Sanghyeok0/mathlib4), where they extend
Mathlib modules directly. This artifact pins the exact source snapshot used by
the paper rather than maintaining a second copy of the Lean files.

## Formalization Snapshot

- Development branch: [`buchberger-formalization`](https://github.com/Sanghyeok0/mathlib4/tree/buchberger-formalization)
- Immutable commit: [`4868fec773dcba035d283904f8b118511cc83d73`](https://github.com/Sanghyeok0/mathlib4/tree/4868fec773dcba035d283904f8b118511cc83d73)
- Generated API documentation: <https://sanghyeok0.github.io/Buchberger/docs/>
- Reproducibility details: [`ARTIFACT.md`](ARTIFACT.md)

The snapshot contains the following six-file development:

1. `Mathlib/Logic/Relation.lean`
2. `Mathlib/Logic/Relation/NormalForm.lean`
3. `Mathlib/RingTheory/MvPolynomial/PolynomialReductions.lean`
4. `Mathlib/RingTheory/MvPolynomial/GroebnerBasisCriterion.lean`
5. `Mathlib/RingTheory/MvPolynomial/BuchbergerCriterion.lean`
6. `Mathlib/RingTheory/MvPolynomial/BuchbergerAlgorithm.lean`

`Buchberger.lean` imports this development from the pinned fork commit. The
`lake-manifest.json` file records the complete dependency graph.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake --dir .lake/packages/mathlib exe cache get \
  --scope=6e95f007303886f3523fdf27b66da9d06acfe42c
lake build
```

No checkout of a moving branch is needed: the dependency is fixed to the full
commit hash above. The optional cache scope is an ancestor PR commit from the
same fork; omit `--scope=...` to rebuild outside that additional cache trust
boundary.

## Paper

The manuscript is in preparation. Its arXiv and archival links will be added
here when the first public version is deposited.

## Legacy Prototype

The earlier standalone implementation and its Lean Blueprint remain available
in the [`legacy-prototype`](https://github.com/Sanghyeok0/Buchberger/tree/legacy-prototype)
branch and at the immutable tag
[`legacy-prototype-v1`](https://github.com/Sanghyeok0/Buchberger/tree/legacy-prototype-v1).
They are preserved for historical reference and are not the source snapshot
used by the current paper.
