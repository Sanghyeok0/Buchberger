# Paper source

This directory is the canonical source for the manuscript
**A Reduction-Theoretic Formalization of Groebner Bases and an Abstract Buchberger Procedure in Lean 4**.

- `manuscript.tex` is the top-level file.
- `sections/` contains the manuscript sections.
- `references.bib` contains the bibliography database.
- `lstlean.tex` contains Lean listings configuration.
- `manuscript.pdf` is the current compiled review PDF and is intentionally committed to Git.

The source files and `manuscript.pdf` should be updated together so that a reader of the `main` branch can inspect both the current LaTeX and the corresponding rendered paper.

## Fast editing in Codespaces

The repository contains a LaTeX-ready devcontainer. Open the repository in GitHub Codespaces; TeX Live, `latexmk`, BibTeX, and the VS Code LaTeX Workshop extension are installed in the container.

Build once:

```sh
./paper/build.sh
```

Continuously rebuild after source changes:

```sh
./paper/watch.sh
```

Open `paper/manuscript.pdf` in the VS Code editor to inspect the rendered paper. The PDF refreshes when the file is rebuilt.

To build, stage the paper source and PDF, commit them, and push in one command, supply a commit message:

```sh
./paper/publish.sh "Revise manuscript wording"
```

LaTeX auxiliary files, `manuscript.bbl`, and `arxiv-source.zip` remain untracked build products.

## Clean build and arXiv package

The GitHub Actions workflow `.github/workflows/paper.yml` is a manual clean-build check. Run it from the Actions tab when a reproducibility check or an arXiv-ready source archive is needed. It produces `manuscript.pdf`, `manuscript.bbl`, and `arxiv-source.zip` as workflow artifacts.

For an arXiv submission snapshot, tag the exact commit (for example `arxiv-v1`) before or immediately after submission.
