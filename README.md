# Buchberger Algorithm Formalization

[![GitHub CI](https://github.com/Sanghyeok0/Buchberger/actions/workflows/push.yml/badge.svg)](https://github.com/Sanghyeok0/Buchberger/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/Sanghyeok0/Buchberger)

This repository contains a Lean 4 formalization of **Buchberger's Algorithm** for computing **Gröbner bases** in polynomial rings. Gröbner bases, introduced by **Bruno Buchberger in 1965**, are a fundamental tool in computational algebra, providing a systematic way to solve polynomial systems.

This project is based on **Lean 4** and **Mathlib**, and aims to **rigorously formalize polynomial ideal theory**, closely following standard references such as *Ideals, Varieties, and Algorithms* [CLO1997] and *Gröbner Bases* [BW1993].

---

## 📖 Documentation

- **Blueprint of the proof**: [📚 Buchberger Blueprint](https://sanghyeok0.github.io/Buchberger/blueprint/)
- **Documentation of the methods**: [📜 Lean API Docs](https://sanghyeok0.github.io/Buchberger/docs/)
- **GitHub Repository**: [🔗 GitHub](https://github.com/Sanghyeok0/Buchberger)
- **Discussion on Zulip**: [💬 Zulip Chat](https://leanprover.zulipchat.com/)

---

## **📂 Project Structure**
- `Buchberger/` - Lean 4 source files  
  - Contains Lean formalizations (e.g., `MonomialIdeal.lean`, `GroebnerBases.lean`)  
- `blueprint/` - Lean Blueprint documentation  
  - `src/` - LaTeX sources for the Blueprint  
    - `chapter/` - Individual chapters in LaTeX  
    - `macros/` - Common and format-specific macros (`common.tex`, `web.tex`, `print.tex`)  
    - `content.tex` - Main Blueprint content file  
  - `web/` - HTML output of the Blueprint (after `leanblueprint web`)  
  - `print/` - PDF output of the Blueprint (after `leanblueprint pdf`)  
- `home_page/` - Jekyll-based GitHub Pages website  
- `lakefile.toml` - Lean 4 package configuration  
- `README.md` - This file!  
- `.github/workflows/` - Continuous integration (CI) for Lean & Blueprint  

---

## **🚀 Build Instructions**

### **🔹 Build the Lean Files**
To compile the Lean 4 code, ensure you have Lean installed.  
Follow the [Lean installation guide](https://leanprover-community.github.io/get_started.html).

### **🔹 Build the Blueprint**
To generate the **Blueprint (formalization document)** and web version, run:
```sh
leanblueprint web
```
To generate the **PDF version**, run:
```
leanblueprint pdf
```
The compiled **PDF document** will be located at:
```
blueprint/print/print.pdf
```

---

## **📌 Source References**

`[CLO1997]`: <https://www.springer.com/gp/book/9780387946801>  
*Cox, Little, and O'Shea*, *Ideals, Varieties, and Algorithms*, Springer, 1997.

`[BW1993]`: <https://www.cambridge.org/core/books/grobner-bases/2A360FC17BB715C2C99402D16A204BD6>  
*Becker and Weispfenning*, *Gröbner Bases*, Cambridge University Press, 1993.