# Explicit Tunable Elegant Joint Measurements for Every Odd Number of Qubits

[中文](README.md) | English

**Author: Tingyu Zhang**  
**Date: 2026-10-30**

This repository contains the complete paper in English and Chinese, the LaTeX sources, exact verification programs, and a Lean formalization.

## Abstract

Elegant joint measurements connect orthogonal global measurement states with regular tetrahedral geometry in local Bloch spheres. Explicit individual constructions are known for arbitrary numbers of qubits, together with continuously tunable families for even numbers. For odd $n\ge5$, a uniform closed-form family passing through the known EJM, preserving fixed regular tetrahedral directions, and continuously varying a common radius had remained to be constructed. This work gives a uniform analytic construction for every odd $n\ge5$: the odd and even interior positions are separately compressed into parity bits, a fixed cubic Boolean function of five variables controls the phase, and a single-point correction is applied only to the physical all-zero string. The resulting $2^n$ states form an orthonormal basis for every real parameter. On $t\in[-\pi/2,\pi/2]$, each qubit has its own parameter-independent set of regular tetrahedral directions, while all qubits and measurement outcomes share the Bloch radius

$$
r_n(t)=\frac{\sqrt3}{2^{n-1}}(1-\sin t).
$$

At $t=0$, the family recovers the known multiqubit EJM state by state. Over the chosen parameter interval, its radius has the exact range $[0,\sqrt3/2^{n-2}]$. The proof separates local expectations into a background with zero single-qubit polarization and interference from a single-point defect, then uses Boolean Fourier cancellation for arbitrary odd $n$. An appendix provides fixed finite character certificates and their general-dimensional reduction. The construction yields continuously tunable single-qubit reduced spectra and connects the known measurement to an endpoint where every single-qubit marginal is maximally mixed.

## Construction and main consequences

The construction uses the established Pauli-orbit and diagonal-phase framework. The same five-variable Boolean rule applies to all odd $n\ge5$; only the parity blocks and the standard CNOT chain depend on the system size. No new search or implicit parameter equation is required for each $n$.

The radius decreases strictly across the chosen interval:

$$
r_n(-\pi/2)=\frac{\sqrt3}{2^{n-2}},\qquad
r_n(0)=\frac{\sqrt3}{2^{n-1}},\qquad
r_n(\pi/2)=0.
$$

The upper endpoint is twice the radius of the known EJM. Each fixed tetrahedral direction label occurs $2^{n-2}$ times at each qubit. At zero radius, the four local points coincide at the Bloch-sphere center, and every single-qubit reduced state equals $I/2$. The stated upper endpoint is the maximum along this constructed path.

## Paper and formalization

- Paper PDF: [English](paper/main-en.pdf) | [Chinese](paper/main.pdf).
- LaTeX source: [English](paper/main-en.tex) | [Chinese](paper/main.tex), with a shared [bibliography](paper/references.bib).
- [Lean guide — Chinese](lean/README.md), [main theorem](lean/OddEJM/Main.lean), and [axiom audit](lean/axioms.txt).

`OddEJM.odd_ejm_family` assumes only $n\ge5$ and `Odd n`. It proves properties of the actual circuit-generated measurement states: orthonormality, projector completeness, all single-qubit partial-trace formulas, tetrahedral geometry, label multiplicities, exact recovery of the original phase construction, and the radius's continuity, strict monotonicity on the stated interval, and exact image. Further theorems establish reduced-matrix multiplicities at nonzero radius, reduced-spectrum eigenvalues, and purity.

The proofs use the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, without `sorry`, custom axioms, or `native_decide`. The paper's base-2 entanglement-entropy formula remains an analytic consequence of the reduced spectrum and is outside the Lean formalization.

## Reproduction

From the repository root, run the exact checks with **Python 3.10+**, using only the standard library:

```text
python paper/verify_certificate.py
python paper/verify_measurement.py
```

These generate the sixteen Walsh certificates and direct gate checks at $n=5,7,9,11$. Finite-size checks cross-check signs and normalization; the analytic and Lean proofs establish the result for arbitrary odd $n\ge5$.

With elan installed, build the project pinned to **Lean 4.35.0 and mathlib v4.35.0**:

```text
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The final command prints theorem types and transitive axiom dependencies. Cache download can be skipped when dependencies are already available.

To rebuild the papers, return to the repository root and use XeLaTeX, latexmk, and BibTeX. The Chinese version additionally requires ctex/Fandol. Both versions have been built with TeX Live 2026:

```text
latexmk -cd -xelatex -interaction=nonstopmode -halt-on-error paper/main-en.tex
latexmk -cd -xelatex -interaction=nonstopmode -halt-on-error paper/main.tex
```
