# Artifact and Reproducibility

## Canonical Source

The formalization extends Mathlib directly and is maintained in
[`Sanghyeok0/mathlib4`](https://github.com/Sanghyeok0/mathlib4). The artifact
for the paper is the immutable commit
[`4868fec773dcba035d283904f8b118511cc83d73`](https://github.com/Sanghyeok0/mathlib4/tree/4868fec773dcba035d283904f8b118511cc83d73)
from the development branch `buchberger-formalization`.

The branch name is provided for orientation only. Reproduction and citations
should use the full commit hash because a branch can move.

## Included Modules

| Layer | Module |
| --- | --- |
| Relation closures and confluence | `Mathlib.Logic.Relation` |
| Normal forms and termination | `Mathlib.Logic.Relation.NormalForm` |
| Polynomial reduction | `Mathlib.RingTheory.MvPolynomial.PolynomialReductions` |
| Groebner basis criterion | `Mathlib.RingTheory.MvPolynomial.GroebnerBasisCriterion` |
| Buchberger criterion | `Mathlib.RingTheory.MvPolynomial.BuchbergerCriterion` |
| Abstract Buchberger procedure | `Mathlib.RingTheory.MvPolynomial.BuchbergerAlgorithm` |

## Reproducing the Build

Clone this repository and build its root module:

```sh
git clone https://github.com/Sanghyeok0/Buchberger.git
cd Buchberger
lake update
lake --dir .lake/packages/mathlib exe cache get \
  --scope=6e95f007303886f3523fdf27b66da9d06acfe42c
lake build
```

The package manager reads `lakefile.toml` and `lake-manifest.json`, checks out
the pinned fork commit, and imports the six modules through `Buchberger.lean`.
The Lean version is fixed by `lean-toolchain`.

The explicit cache scope is the paper branch's already-verified PR ancestor in
the same fork. It is only a build accelerator: omitting the option causes Lake
to rebuild artifacts unavailable in its default cache and does not change the
source revision or theorem checking.

For a direct check of the final module in the source repository:

```sh
git clone https://github.com/Sanghyeok0/mathlib4.git
cd mathlib4
git checkout 4868fec773dcba035d283904f8b118511cc83d73
lake exe cache get
lake env lean Mathlib/RingTheory/MvPolynomial/BuchbergerAlgorithm.lean
```

## Documentation

GitHub Actions builds declaration-level documentation with doc-gen4 and
publishes it at <https://sanghyeok0.github.io/Buchberger/docs/>. Source links
in the paper should target this documentation or the immutable fork commit.

## Historical Development

The original standalone implementation and Blueprint are archived in the
`legacy-prototype` branch and the `legacy-prototype-v1` tag. They are not part
of the current paper artifact.
