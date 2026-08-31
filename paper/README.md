# Paper source

This directory is the canonical source for the manuscript
**A Reduction-Theoretic Formalization of Groebner Bases and an Abstract Buchberger Procedure in Lean 4**.

- `manuscript.tex` is the top-level file.
- `sections/` contains the manuscript sections.
- `references.bib` contains the bibliography database.
- `lstlean.tex` contains Lean listings configuration.

The GitHub Actions workflow `.github/workflows/paper.yml` compiles the PDF and creates an arXiv-ready source archive. Generated PDF, BBL, and ZIP files are build artifacts and are not committed to Git.

For an arXiv submission snapshot, tag the exact commit (for example `arxiv-v1`) before or immediately after submission.
