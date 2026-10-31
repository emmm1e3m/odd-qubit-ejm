# Verification record

Version: October 31, 2026.

| Check | Result |
|---|---|
| English and Chinese manuscripts | Compiled in REVTeX 4.2 PRA format; 15 and 16 pages. All 31 pages were visually inspected, and 115 displayed formulas and their numbering were compared between languages. The title, abstracts, narrative flow, literature terminology, and qubit-count notation were revised; an independent comparison confirmed that mathematical statements and assumptions were preserved. The final abstracts were separately checked against the theorem statements and for bilingual consistency; both PDFs were rebuilt and inspected afterward. |
| Lean source package | 77 `UnifiedEJM` modules and 28 required foundation modules; Lean 4.35.0 and mathlib v4.35.0. The complete project builds successfully. |
| Public axiom audit | All 72 declarations in `lean-unified/Audit.lean` passed. Dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`. |
| Proof placeholders | No `sorry`, custom axioms, or `native_decide` in the supplied proof sources. |
| Exact recomputation | All seven checks passed. Calculations use exact finite sums, Laurent polynomials, rational arithmetic, and symbolic identities. |
| Independent review | The analytic argument, bilingual manuscript, physical meaning of the formal objects, and theorem assumptions were independently reviewed; the resulting corrections were incorporated. |

The [coverage table](lean-unified/COVERAGE.md) maps manuscript statements to precise declarations. The public [audit output](lean-unified/axioms.txt) displays theorem types and transitive axiom dependencies. The [exact computation results](paper/reproduce/verification_results.json) accompany the [reproduction instructions](paper/reproduce/README.md).

Finite-dimensional checks include 1,280 Gram-matrix entries and 224 actual partial-trace matrices. Statements for arbitrary qubit number and entire continuous parameter intervals are proved analytically and in Lean; these finite checks supply an additional comparison with the original circuit definitions.

Build and audit from `lean-unified/`:

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

The adjacent `lean/` directory contains only the foundation modules needed by the current proof. Obsolete manuscript files, old finite-check programs, and unused old theorem modules have been removed from the working version; the earlier version remains in Git history.
